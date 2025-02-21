#![allow(non_snake_case)]
use ark_std::log2;
use folding_schemes::arith::ccs::CCS;
use folding_schemes::utils::vec::hadamard;
use folding_schemes::utils::vec::mat_vec_mul;
use folding_schemes::utils::vec::SparseMatrix;
use halo2_proofs::circuit::Value;
use halo2_proofs::dump::dump_gates;
use halo2_proofs::dump::dump_lookups;
use halo2_proofs::dump::AssignmentDumper;
use halo2_proofs::dump::CopyConstraint;
use halo2_proofs::plonk;
use halo2_proofs::plonk::*;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;

mod query;
use query::*;
mod monomial;
use monomial::*;
mod lookup;

// Basic flow of the Plonkish -> CCS+ conversion process in this code is
// 1. Populate HashMap<AbsoluteCellPosition, CCSValue> with the assignments extracted from a Halo2 circuit
// 2. Modify the HashMap according to copy constraints
// 3. Populate the Z vector according to HashMap
// 4. Generate M_j from custom gates extracted from a Halo2 circuit

// Notes on lookup:
// Halo2 allows us to constrain an Expression evaluated at each row to be in a lookup table.
// Halo2 calls such Expression a lookup input.
// Halo2 stores these evaluation result sepalately from the assignments in the table.
// But in the case of CCS+, these evaluation results has to be in Z, and we need to commit to it together with other columns.
// Thus in this code I treat a lookup input evaluated at each row as if it's another column.
// I later constrain these lookup input evaluation result columns according to the lookup input Expression, just like we constrain advice columns according to custom gate Expression.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CCSValue<F: ark_ff::PrimeField> {
    InsideZ(usize), // z_index
    InsideM(F),     // fixed value
}

// A mapping from absolute cell position in the original table (column_type, column_index, row_index)
// to the position in Z
fn generate_cell_mapping<HALO2: ff::PrimeField<Repr = [u8; 32]>, ARKWORKS: ark_ff::PrimeField>(
    // These have to have the shape [[cell assignment; number of rows]; number of columns]
    // None means unassigned cell
    instance: &[&[Option<HALO2>]],
    advice: &[&[Option<HALO2>]],
    fixed: &[&[Option<HALO2>]],
    selectors: &[&[bool]],
    copy_constraints: &[CopyConstraint],
    lookup_inputs: &[Expression<HALO2>],
) -> HashMap<AbsoluteCellPosition, CCSValue<ARKWORKS>> {
    let mut cell_mapping: HashMap<AbsoluteCellPosition, CCSValue<ARKWORKS>> = HashMap::new();
    let mut z_height = 1;

    for (column_index, column) in instance.into_iter().enumerate() {
        for (row_index, _) in column.into_iter().enumerate() {
            let cell_position = AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index,
                row_index,
            };
            cell_mapping.insert(cell_position, CCSValue::InsideZ(z_height));
            z_height += 1;
        }
    }

    for (column_index, column) in advice.into_iter().enumerate() {
        for (row_index, _) in column.into_iter().enumerate() {
            let cell_position = AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index,
                row_index,
            };
            cell_mapping.insert(cell_position, CCSValue::InsideZ(z_height));
            z_height += 1;
        }
    }

    for (column_index, column) in fixed.into_iter().enumerate() {
        for (row_index, cell) in column.into_iter().enumerate() {
            // Here we initialize unassigned fixed cell with 0.
            // This mimics Halo2's behavior.
            // https://github.com/zcash/halo2/blob/fed6b000857f27e23ddb07454da8bde4697204f7/halo2_proofs/src/poly/domain.rs#L189
            let value = ARKWORKS::from_le_bytes_mod_order(&cell.unwrap_or(0.into()).to_repr());
            let cell_position = AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index,
                row_index,
            };
            cell_mapping.insert(cell_position, CCSValue::InsideM(value));
        }
    }

    for (column_index, column) in selectors.into_iter().enumerate() {
        for (row_index, cell) in column.into_iter().enumerate() {
            let value = (*cell).into();
            let cell_position = AbsoluteCellPosition {
                column_type: VirtualColumnType::Selector,
                column_index,
                row_index,
            };
            cell_mapping.insert(cell_position, CCSValue::InsideM(value));
        }
    }

    // Next, incorporate the copy constraints into the mapping.
    deduplicate_witness(&mut cell_mapping, copy_constraints);

    // Next, incorporate lookup constraints into the mapping.
    let table_height = advice[0].len();
    for (lookup_index, lookup_input) in lookup_inputs.iter().enumerate() {
        for y in 0..table_height {
            let key = AbsoluteCellPosition {
                column_type: VirtualColumnType::LookupInput,
                column_index: lookup_index,
                row_index: y,
            };
            let value = match lookup_input {
                // If the lookup input is just a query, we don't add new witness to Z.
                // Instead we store in cell_mapping a reference to an existing entry in Z.
                Expression::Advice(query) => cell_mapping
                    .get(&Query::Advice(*query).cell_position(y, table_height))
                    .copied()
                    .unwrap(),
                Expression::Instance(query) => cell_mapping
                    .get(&Query::Instance(*query).cell_position(y, table_height))
                    .copied()
                    .unwrap(),
                // If the lookup input is a complex Expression, we will create new witness
                _ => {
                    z_height += 1;
                    CCSValue::InsideZ(z_height - 1)
                }
            };
            cell_mapping.insert(key, value);
        }
    }

    cell_mapping
}

// Cells with greater ordering will get deduplicated into cells with less ordering.
fn deduplicate_witness<F: ark_ff::PrimeField>(
    cell_mapping: &mut HashMap<AbsoluteCellPosition, CCSValue<F>>,
    copy_constraints: &[CopyConstraint],
) {
    // Each element in HashSet<AbsoluteCellPosition> must have the same assignment.
    let mut equalities: Vec<HashSet<AbsoluteCellPosition>> = Vec::new();

    for copy_constraint in copy_constraints.into_iter() {
        // These 2 cells must have the same assignment.
        let cell1 = AbsoluteCellPosition {
            column_type: copy_constraint.from_column_type.into(),
            column_index: copy_constraint.from_column_index,
            row_index: copy_constraint.from_row_index,
        };
        let cell2 = AbsoluteCellPosition {
            column_type: copy_constraint.to_column_type.into(),
            column_index: copy_constraint.to_column_index,
            row_index: copy_constraint.to_row_index,
        };

        // The use of .iter().position() here must slow down the code, but I prioritize the readability of the code.
        let cell1_belongs_in = equalities
            .iter()
            .position(|must_be_same| must_be_same.contains(&cell1));
        let cell2_belongs_in = equalities
            .iter()
            .position(|must_be_same| must_be_same.contains(&cell2));

        match (cell1_belongs_in, cell2_belongs_in) {
            (None, None) => {
                // When neither of the cells are in `equalities`, we add a new entry.
                equalities.push(HashSet::new());
                equalities.last_mut().unwrap().insert(cell1);
                equalities.last_mut().unwrap().insert(cell2);
            }
            (Some(cell1_belongs_in), None) => {
                // When we encounter a new copy constraint A = B when we already have B = C,
                // `equalities` must be updated to be [A = B = C], not [A = B, B = C]
                equalities[cell1_belongs_in].insert(cell2);
            }
            (None, Some(cell2_belongs_in)) => {
                equalities[cell2_belongs_in].insert(cell1);
            }
            (Some(cell1_belongs_in), Some(cell2_belongs_in)) => {
                // Let's say we have `equalities` [A = C, B = C].
                // And then we encountered a new copy constraint A = B.
                // Then the new `equalities` must be [A = B = C], not [A = C, B = C, A = B].
                let to_be_merged = equalities.remove(cell2_belongs_in);
                equalities[cell1_belongs_in].extend(to_be_merged);
            }
        }
    }

    for must_be_same in equalities.into_iter() {
        let mut sorted: Vec<AbsoluteCellPosition> = must_be_same.into_iter().collect();
        sorted.sort();

        // For each equality set, we deduplicate into the cell position with the least ordering.
        let deduplicate_into = sorted.first().unwrap();
        // It's okay to unwrap here because an element of `equalities` will never have length fewer than 2.

        for deduplicate_from in sorted.iter().skip(1) {
            *cell_mapping.get_mut(&deduplicate_from).unwrap() =
                cell_mapping.get(&deduplicate_into).copied().unwrap();
        }
    }
}

#[cfg(test)]
#[test]
fn test_duplicate_witness() {
    use ark_pallas::Fq;

    let mut actual: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = HashMap::new();
    actual.insert(
        // cell A
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 0,
        },
        CCSValue::InsideZ(1),
    );
    actual.insert(
        // cell B
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 1,
        },
        CCSValue::InsideZ(2),
    );
    actual.insert(
        // cell C
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 2,
        },
        CCSValue::InsideZ(3),
    );
    actual.insert(
        // cell D
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 3,
        },
        CCSValue::InsideZ(4),
    );

    let copy_constraints = vec![
        CopyConstraint {
            // B = C
            from_column_type: Any::Advice,
            from_column_index: 0,
            from_row_index: 2,
            to_column_type: Any::Advice,
            to_column_index: 0,
            to_row_index: 1,
        },
        CopyConstraint {
            // C = D
            from_column_type: Any::Advice,
            from_column_index: 0,
            from_row_index: 3,
            to_column_type: Any::Advice,
            to_column_index: 0,
            to_row_index: 2,
        },
        CopyConstraint {
            // B = A
            from_column_type: Any::Advice,
            from_column_index: 0,
            from_row_index: 0,
            to_column_type: Any::Advice,
            to_column_index: 0,
            to_row_index: 1,
        },
    ];

    deduplicate_witness(&mut actual, &copy_constraints);

    // All get deduplicated into A
    let mut expect = HashMap::new();
    expect.insert(
        // cell A
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 0,
        },
        CCSValue::InsideZ(1),
    );
    expect.insert(
        // cell B
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 1,
        },
        CCSValue::InsideZ(1),
    );
    expect.insert(
        // cell C
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 2,
        },
        CCSValue::InsideZ(1),
    );
    expect.insert(
        // cell D
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 3,
        },
        CCSValue::InsideZ(1),
    );

    assert_eq!(actual, expect);
}

#[cfg(test)]
#[test]
fn test_duplicate_witness_instance() {
    use ark_pallas::Fq;

    let mut actual: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = HashMap::new();
    actual.insert(
        // cell A
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 0,
        },
        CCSValue::InsideZ(1),
    );
    actual.insert(
        // cell B
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 1,
        },
        CCSValue::InsideZ(2),
    );
    actual.insert(
        // cell C
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 2,
        },
        CCSValue::InsideZ(3),
    );
    actual.insert(
        // cell D
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Instance,
            column_index: 0,
            row_index: 0,
        },
        CCSValue::InsideZ(4),
    );

    let copy_constraints = vec![
        CopyConstraint {
            // B = C
            from_column_type: Any::Advice,
            from_column_index: 0,
            from_row_index: 2,
            to_column_type: Any::Advice,
            to_column_index: 0,
            to_row_index: 1,
        },
        CopyConstraint {
            // C = D
            from_column_type: Any::Instance,
            from_column_index: 0,
            from_row_index: 0,
            to_column_type: Any::Advice,
            to_column_index: 0,
            to_row_index: 2,
        },
        CopyConstraint {
            // B = A
            from_column_type: Any::Advice,
            from_column_index: 0,
            from_row_index: 0,
            to_column_type: Any::Advice,
            to_column_index: 0,
            to_row_index: 1,
        },
    ];

    deduplicate_witness(&mut actual, &copy_constraints);

    // All get deduplicated into D
    let mut expect = HashMap::new();
    expect.insert(
        // cell A
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 0,
        },
        CCSValue::InsideZ(4),
    );
    expect.insert(
        // cell B
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 1,
        },
        CCSValue::InsideZ(4),
    );
    expect.insert(
        // cell C
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Advice,
            column_index: 0,
            row_index: 2,
        },
        CCSValue::InsideZ(4),
    );
    expect.insert(
        // cell D
        AbsoluteCellPosition {
            column_type: VirtualColumnType::Instance,
            column_index: 0,
            row_index: 0,
        },
        CCSValue::InsideZ(4),
    );

    assert_eq!(actual, expect);
}

fn generate_mj<F: ark_ff::PrimeField>(
    query: Query,
    table_height: usize,
    z_height: usize,
    cell_mapping: &HashMap<AbsoluteCellPosition, CCSValue<F>>,
) -> SparseMatrix<F> {
    let mut mj = SparseMatrix::empty();
    mj.n_cols = z_height;
    mj.n_rows = table_height;
    // might increase later when there was multiple custom gates.

    for y in 0..table_height {
        let cell_position = query.cell_position(y, table_height);

        let ccs_value = cell_mapping.get(&cell_position).unwrap();
        match ccs_value {
            CCSValue::InsideZ(z_index) => {
                // If the query refers to an instance or advice cell
                // mj[y, z_index] = 1
                mj.coeffs.push(Vec::new());
                mj.coeffs.last_mut().unwrap().push((F::one(), *z_index));
            }
            CCSValue::InsideM(value) => {
                // If the query refers to an fixed or selector cell
                // mj[y, 0] = value
                mj.coeffs.push(Vec::new());
                mj.coeffs.last_mut().unwrap().push((*value, 0));
            }
        }
    }

    mj
}

// Generate a CCS instance that works, but unoptimized.
fn generate_naive_ccs_instance<HALO2: ff::PrimeField<Repr = [u8; 32]>, F: ark_ff::PrimeField>(
    custom_gates: &[Expression<HALO2>],
    cell_mapping: &HashMap<AbsoluteCellPosition, CCSValue<F>>,
    lookup_inputs: &[Expression<HALO2>],
) -> CCS<F> {
    let table_height = cell_mapping
        .keys()
        .map(|cell_position| cell_position.row_index + 1)
        .max()
        .expect("Empty cell_mapping");
    let z_height = cell_mapping
        .values()
        .map(|ccs_value| match ccs_value {
            CCSValue::InsideZ(z_index) => *z_index + 1,
            CCSValue::InsideM(_) => 0,
        })
        .max()
        .expect("Empty cell mapping");
    let num_instance_cells: usize = cell_mapping
        .keys()
        .map(|cell_position| {
            if cell_position.column_type == VirtualColumnType::Instance {
                1
            } else {
                0
            }
        })
        .sum();

    let mut gates: Vec<Vec<Monomial<F>>> = custom_gates
        .iter()
        .map(|gate| get_monomials(gate))
        .collect();
    gates.extend(
        lookup_inputs
            .iter()
            .enumerate()
            .filter_map(|(lookup_index, expr)| match expr {
                // If the lookup input is just a query, we don't add new witness to Z.
                // Thus we don't have to add new constraints.
                Expression::Advice(_) => None,
                Expression::Instance(_) => None,
                // If the lookup input is a complex Expression, we will create new witness, and constrain those witnesses according to the Expression<F>
                _ => {
                    let mut monomials = vec![Monomial {
                        // here I'm constraining for each row
                        // expr - Z[z_index where the lookup input lies] = 0
                        coefficient: -F::one(),
                        variables: vec![Query::LookupInput(lookup_index)],
                    }];
                    monomials.extend(get_monomials(expr));
                    Some(monomials)
                }
            }),
    );

    let m = gates.len() * table_height;

    let mut M: Vec<SparseMatrix<F>> = Vec::new();
    let mut c: Vec<F> = Vec::new();
    let mut S: Vec<Vec<usize>> = Vec::new();

    for (gate_index, monomials) in gates.iter().enumerate() {
        for monomial in monomials.iter() {
            c.push(monomial.coefficient);
            S.push(Vec::new());

            for query in monomial.variables.iter() {
                // Shift the m_j down

                // M_j for first gate would look like
                // |100|
                // |010|
                // |001|
                // |000|
                // |000|
                // |000|

                // M_j for second gate would look like
                // |000|
                // |000|
                // |000|
                // |100|
                // |010|
                // |001|

                let mut mj = generate_mj(*query, table_height, z_height, &cell_mapping);
                mj.n_rows = m;

                let y_offset = gate_index * table_height;
                let mut new_coeffs = vec![vec![]; m];
                new_coeffs[y_offset..(y_offset + mj.coeffs.len())].clone_from_slice(&mj.coeffs);
                mj.coeffs = new_coeffs;

                S.last_mut().unwrap().push(M.len());
                M.push(mj);
            }
        }
    }

    CCS {
        m,
        n: z_height,
        l: num_instance_cells,
        t: M.len(),
        q: S.len(),
        d: S.iter().map(|multiset| multiset.len()).max().unwrap_or(1),
        s: log2(table_height) as usize,
        s_prime: log2(z_height) as usize,
        M,
        S,
        c,
    }
}

fn generate_ccs_instance<HALO2: ff::PrimeField<Repr = [u8; 32]>, F: ark_ff::PrimeField>(
    custom_gates: &[Expression<HALO2>],
    cell_mapping: &mut HashMap<AbsoluteCellPosition, CCSValue<F>>,
    lookup_inputs: &[Expression<HALO2>],
) -> CCS<F> {
    let mut ccs = generate_naive_ccs_instance(custom_gates, cell_mapping, lookup_inputs);
    reduce_d(&mut ccs);
    reduce_t(&mut ccs);
    reduce_n(&mut ccs, cell_mapping);
    ccs
}

// This function optimizes a CCS instance.
// Reduces the degree of a CCS instance.
fn reduce_d<F: ark_ff::PrimeField>(ccs: &mut CCS<F>) {
    let mut M: Vec<SparseMatrix<F>> = Vec::new();
    let mut S: Vec<Vec<usize>> = Vec::new();

    for monomial in ccs.S.iter() {
        S.push(Vec::new());

        let mj_for_monomial: Vec<&SparseMatrix<F>> =
            monomial.iter().map(|index| &ccs.M[*index]).collect();
        // M matrices generated from FixedQuery or Selector
        let mut mj_static: Vec<&SparseMatrix<F>> = Vec::new();
        // M matrices generated from AdviceQuery or InstanceQuery
        let mut mj_dynamic: Vec<SparseMatrix<F>> = Vec::new();

        for mj in mj_for_monomial {
            if mj.coeffs.iter().all(|row| {
                // Either the row is a 0 vector, or only the first element of the row is filled
                row.iter().all(|elem| {
                    F::from(0) == elem.0 // either the value is 0
                        || elem.1 == 0 // or the row index is 0
                })
            }) {
                mj_static.push(mj);
            } else {
                mj_dynamic.push(mj.clone());
            }
        }

        if 0 >= mj_static.len() {
            // When a monomial has no query into fixed columns, we add M matrices into the CCS instance.
            // This is the simplest case.
            S.last_mut()
                .unwrap()
                .extend(M.len()..(M.len() + mj_dynamic.len()));
            M.extend(mj_dynamic);
        } else {
            // Consider the case where a monomial has multiple queries into fixed columns.
            // custom gate: FixedColumn1 * FixedColumn2 * AdviceColumn1 = 0
            // Then a naive implementation would generate 2 M matrices for fixed columns, and 1 for an advice column,
            // We *batch* the M matrices for fixed columns, by multiplying it beforehand, and generate one single M matrix for multiple fixed columns.
            // This way we can reduce the degree of the custom gate in the CCS instance.
            let batched_vec: Vec<F> = mj_static
                .into_iter()
                .map(|mj| {
                    // only the first column of a M matrix for a fixed column is filled.
                    // So this way I can get the first column of mj as a vector
                    mat_vec_mul(&mj, &vec![1.into(); mj.n_cols]).unwrap()
                })
                .reduce(|acc, new| hadamard(&acc, &new).unwrap())
                .unwrap();
            // By the condition of the if clause 0 < mj_static.len() so this reduce will never return None.

            if 0 >= mj_dynamic.len() {
                // When a monomial has no query into advice/instance columns, we'll add the batched M matrix to the CCS instance, and we're done.
                let mut mj_static_batched: SparseMatrix<F> = SparseMatrix::empty();
                mj_static_batched.n_cols = ccs.n;
                mj_static_batched.n_rows = ccs.m;
                mj_static_batched.coeffs = batched_vec.into_iter().map(|x| vec![(x, 0)]).collect();

                S.last_mut().unwrap().push(M.len());
                M.push(mj_static_batched);
            } else {
                // When a monomial has queries into both fixed/selector columns and advice/instance columns, we can further batch M matrices.
                // By baking the fixed multiplication into one of the M matrices for advice/instance columns.
                mj_dynamic.first_mut().unwrap().coeffs = mj_dynamic
                    .first()
                    .unwrap()
                    .coeffs
                    .iter()
                    .zip(batched_vec.iter())
                    .map(|(mj_row, multiply_row_by)| {
                        mj_row
                            .into_iter()
                            .map(|(elem, pos)| (*elem * multiply_row_by, *pos))
                            .collect()
                    })
                    .collect();

                for mj in mj_dynamic.iter_mut().skip(1) {
                    // Consider a custom gate F1 * A1 * A2 = 0
                    // where F1 is a fixed column, A1 and A2 are advice columns.
                    // In this case, baking the fixed multiplication into M matrices for both A1 and A2 will result in redundant double multiplications.
                    // However, when a fixed cell takes a value 0, it's okay to bake the fixed 0 multiplication into M matrices for both A1 and A2, since 0 * A1 * A2 = 0 * A1 * 0 * A2.
                    // So we do it here.
                    // You might ask why we need to do this.
                    // It will become important when we later implement detection of unused witnesses in Z.
                    for (row_mj, multiply_row_by) in mj.coeffs.iter_mut().zip(batched_vec.iter()) {
                        if *multiply_row_by == 0.into() {
                            *row_mj = row_mj
                                .into_iter()
                                .map(|(_, pos)| (0.into(), *pos))
                                .collect();
                        }
                    }
                }

                // Then we add M matrices for advice/instance columns into the CCS instance.
                // We no longer need to add M matrices for fixed columns to the CCS instance because it's already baked into the M matrices for advice/instance columns.
                S.last_mut()
                    .unwrap()
                    .extend(M.len()..(M.len() + mj_dynamic.len()));
                M.extend(mj_dynamic);
            }
        }
    }

    ccs.t = M.len();
    ccs.d = S.iter().map(|multiset| multiset.len()).max().unwrap_or(1);
    ccs.M = M;
    ccs.S = S;
}

// This function optimizes a CCS instance.
// Reduces the number of M matrices in a CCS instance.
fn reduce_t<F: ark_ff::PrimeField>(ccs: &mut CCS<F>) {
    // There are 2 ways an element at (x,y) in a SparseMatrix can be 0
    // 1. SparseMatrix.coeffs[y] contains (0, x)
    // 2. SparseMatrix.coeffs[y] does not contain (0, x), but (non-0, x) doesn't exist either, so it's implied that the element at (x,y) is 0
    // Thus the same SparseMatrix can take many forms on the memory.
    // It's cumbersome to handle 2 cases so here we sanitize SparseMatrix, into the case 2.
    for mj in ccs.M.iter_mut() {
        for row in mj.coeffs.iter_mut() {
            row.retain(|elem| elem.0 != 0.into());
        }
    }

    let mut M: Vec<SparseMatrix<F>> = Vec::new();
    let mut S: Vec<Vec<usize>> = Vec::new();

    for monomial in ccs.S.iter() {
        S.push(Vec::new());

        for index in monomial {
            let mj = &ccs.M[*index];
            if let Some(j) = M.iter().position(|existing| mj == existing) {
                // If the matrix is already in M, we'll reuse the matrix.
                S.last_mut().unwrap().push(j);
            } else {
                // If the matrix is not yet in M, we'll put it in there.
                S.last_mut().unwrap().push(M.len());
                M.push(mj.clone());
            }
        }
    }

    ccs.t = M.len();
    ccs.M = M;
    ccs.S = S;
}

// This function optimizes a CCS instance.
// Reduces the number of witnesses.
fn reduce_n<F: ark_ff::PrimeField>(
    ccs: &mut CCS<F>,
    cell_mapping: &mut HashMap<AbsoluteCellPosition, CCSValue<F>>,
) {
    let mut used_z: HashSet<usize> = HashSet::new();
    used_z.insert(0);

    for mj in ccs.M.iter() {
        for row in mj.coeffs.iter() {
            for elem in row.iter() {
                // When we encounter a non-0 element in M matrices, mark the column index of that element.
                used_z.insert(elem.1);
            }
        }
    }

    let mut used_z: Vec<usize> = used_z.into_iter().collect();
    used_z.sort();
    // for used_z[i] that is an old z_index, i is the new z_index

    // Update M matrices based on the information we have gathered
    for mj in ccs.M.iter_mut() {
        mj.n_cols = used_z.len();

        for row in mj.coeffs.iter_mut() {
            for elem in row.iter_mut() {
                let new_z_index = used_z
                    .iter()
                    .position(|old_z_index| *old_z_index == elem.1)
                    .unwrap();
                // It's safe to unwrap here because we have sanitized M matrices earlier.
                elem.1 = new_z_index;
            }
        }
    }

    let mut unconstrained_cells: Vec<AbsoluteCellPosition> = Vec::new();

    // Update cell_mapping based on the information we have gathered
    // This is needed because the lookup implementation needs that we can query cell_mapping[cell position] and get the z_index of that cell.
    // If we don't do this the consistency between cell_mapping and Z breaks.
    for (cell_position, ccs_value) in cell_mapping.iter_mut() {
        if let CCSValue::InsideZ(z_index) = ccs_value {
            if let Some(new_z_index) = used_z
                .iter()
                .position(|old_z_index| *old_z_index == *z_index)
            {
                *z_index = new_z_index;
            } else {
                unconstrained_cells.push(*cell_position);
            }
        }
    }

    for unconstrained_cell in unconstrained_cells.iter() {
        cell_mapping.remove(unconstrained_cell);
    }

    ccs.n = used_z.len();
    ccs.l -= unconstrained_cells
        .into_iter()
        .filter(|cell| cell.column_type == VirtualColumnType::Instance)
        .count();
}

fn generate_z<HALO2: ff::PrimeField<Repr = [u8; 32]>, ARKWORKS: ark_ff::PrimeField>(
    selector: &[&[bool]],
    fixed: &[&[Option<HALO2>]],
    instance: &[&[Option<HALO2>]],
    advice: &[&[Option<HALO2>]],
    cell_mapping: &HashMap<AbsoluteCellPosition, CCSValue<ARKWORKS>>,
    lookup_inputs: &[Expression<HALO2>],
) -> Vec<ARKWORKS> {
    let table_height = advice[0].len();
    let z_height = cell_mapping
        .values()
        .map(|ccs_value| match ccs_value {
            CCSValue::InsideZ(z_index) => *z_index + 1,
            CCSValue::InsideM(_) => 0,
        })
        .max()
        .expect("|Z| must be above 2");

    // Here we initialize unassigned cells in the original Plonkish table with 0.
    // This mimics Halo2's behavior.
    // https://github.com/zcash/halo2/issues/614
    let mut z: Vec<ARKWORKS> = vec![0.into(); z_height];
    z[0] = 1.into();

    let mut cells: Vec<AbsoluteCellPosition> = cell_mapping.keys().copied().collect();
    cells.sort();
    cells.reverse();
    // We need to sort and reverse here because
    // when an element in Z represents more than 2 cells in the original Plonkish table due to copy constraints
    // the value in AbsoluteCellPosition with less ordering should take precedence

    for cell_position in cells.iter() {
        let cell_value = match cell_position.column_type {
            VirtualColumnType::Advice => {
                advice[cell_position.column_index][cell_position.row_index]
            }
            VirtualColumnType::Instance => {
                instance[cell_position.column_index][cell_position.row_index]
            }
            VirtualColumnType::LookupInput => lookup_inputs[cell_position.column_index].evaluate(
                &|constant| Some(constant),
                &|query: Selector| {
                    if selector[query.0][cell_position.row_index] {
                        Some(1.into())
                    } else {
                        Some(0.into())
                    }
                },
                &|query: FixedQuery| {
                    fixed[query.column_index][(cell_position.row_index as i32 + query.rotation.0)
                        .rem_euclid(table_height as i32)
                        as usize]
                },
                &|query: AdviceQuery| {
                    advice[query.column_index][(cell_position.row_index as i32 + query.rotation.0)
                        .rem_euclid(table_height as i32)
                        as usize]
                },
                &|query: InstanceQuery| {
                    instance[query.column_index][(cell_position.row_index as i32 + query.rotation.0)
                        .rem_euclid(table_height as i32)
                        as usize]
                },
                &|x| x.map(|x| -x),
                &|lhs, rhs| lhs.and_then(|lhs| rhs.map(|rhs| lhs + rhs)),
                &|lhs, rhs| lhs.and_then(|lhs| rhs.map(|rhs| lhs * rhs)),
                &|lhs, constant| lhs.map(|lhs| lhs * constant),
            ),
            _ => continue,
        };
        if let CCSValue::InsideZ(z_index) = cell_mapping.get(&cell_position).copied().unwrap() {
            if let Some(cell_value) = cell_value {
                z[z_index] = ARKWORKS::from_le_bytes_mod_order(&cell_value.to_repr());
            }
        }
    }

    z
}

/// Converts a Halo2 circuit into a sonobe CCS instance.
///
/// * `k` log_2(the height of the Plonkish table)
/// * `c` A Halo2 circuit you wish to convert
/// * `instance` Assignments to the instance columns. The length of this slice must equal the number of the instance columns in `c`.
///
/// Returns a pair of (a ccs instance, the witness vector Z, and lookup constraints)
/// lookup constraints takes a form of Vec<(L, T)> where for every o ∈ L, z[o] must be in T
pub fn convert_halo2_circuit<
    HALO2: ff::PrimeField<Repr = [u8; 32]>,
    C: Circuit<HALO2>,
    ARKWORKS: ark_ff::PrimeField,
>(
    k: u32,
    circuit: &C,
    instance: &[&[HALO2]],
) -> Result<
    (
        CCS<ARKWORKS>,
        Vec<ARKWORKS>,
        Vec<(HashSet<usize>, HashSet<ARKWORKS>)>,
    ),
    plonk::Error,
> {
    let mut meta = ConstraintSystem::<HALO2>::default();
    let config = C::configure(&mut meta);

    // both AssignmentDumper and generate_ccs_instance expects Vec of length 2^k
    // so I need to fill the vec
    let instance_option: Vec<Vec<Option<HALO2>>> = instance
        .iter()
        .map(|cells| {
            let mut column = vec![None; 1 << k];
            column[0..cells.len()]
                .copy_from_slice(&cells.iter().map(|cell| Some(*cell)).collect::<Vec<_>>());
            column
        })
        .collect();
    let instance_value: Vec<Vec<Value<HALO2>>> = instance
        .iter()
        .map(|cells| {
            let mut column = vec![Value::unknown(); 1 << k];
            column[0..cells.len()].copy_from_slice(
                &cells
                    .iter()
                    .map(|cell| Value::known(*cell))
                    .collect::<Vec<_>>(),
            );
            column
        })
        .collect();

    let mut cell_dumper: AssignmentDumper<HALO2> = AssignmentDumper::new(k, &meta);
    cell_dumper.instance = instance_value;
    C::FloorPlanner::synthesize(&mut cell_dumper, circuit, config, meta.constants.clone())?;

    // FIXME: Isn't there a better way to make &[&[A]] from Vec<Vec<A>>?
    let instance_option: Vec<&[Option<HALO2>]> =
        instance_option.iter().map(Vec::as_slice).collect();
    let advice: Vec<&[Option<HALO2>]> = cell_dumper
        .advice
        .iter()
        .map(|x| x.as_slice())
        .collect::<Vec<_>>();
    let fixed: Vec<&[Option<HALO2>]> = cell_dumper
        .fixed
        .iter()
        .map(|x| x.as_slice())
        .collect::<Vec<_>>();
    let selectors: Vec<&[bool]> = cell_dumper
        .selectors
        .iter()
        .map(|x| x.as_slice())
        .collect::<Vec<_>>();

    dbg!(cell_dumper.copy_constraints.len());

    let lookups = dump_lookups::<HALO2, C>()?;
    let lookup_inputs: Vec<Expression<HALO2>> =
        lookups.iter().map(|(input, _)| input).cloned().collect();
    let mut cell_mapping = generate_cell_mapping(
        &instance_option,
        &advice,
        &fixed,
        &selectors,
        &cell_dumper.copy_constraints,
        &lookup_inputs,
    );

    let custom_gates = dump_gates::<HALO2, C>()?;
    let ccs_instance: CCS<ARKWORKS> =
        generate_ccs_instance(&custom_gates, &mut cell_mapping, &lookup_inputs);
    let z: Vec<ARKWORKS> = generate_z(
        &selectors,
        &fixed,
        &instance_option,
        &advice,
        &cell_mapping,
        &lookup_inputs,
    );

    let tables: Vec<HashSet<ARKWORKS>> = lookups
        .iter()
        .map(|(_, table_expr)| {
            (0..1 << k)
                .map(|at_row| {
                    let scalar = table_expr
                        .evaluate(
                            &|constant| Some(constant),
                            &|query: Selector| {
                                if selectors[query.0][at_row] {
                                    Some(1.into())
                                } else {
                                    Some(0.into())
                                }
                            },
                            &|query: FixedQuery| {
                                fixed[query.column_index][(at_row as i32 + query.rotation.0)
                                    .rem_euclid((1 << k) as i32)
                                    as usize]
                            },
                            &|query: AdviceQuery| {
                                advice[query.column_index][(at_row as i32 + query.rotation.0)
                                    .rem_euclid((1 << k) as i32)
                                    as usize]
                            },
                            &|query: InstanceQuery| {
                                instance_option[query.column_index][(at_row as i32
                                    + query.rotation.0)
                                    .rem_euclid((1 << k) as i32)
                                    as usize]
                            },
                            &|x| x.map(|x| -x),
                            &|lhs, rhs| lhs.and_then(|lhs| rhs.map(|rhs| lhs + rhs)),
                            &|lhs, rhs| lhs.and_then(|lhs| rhs.map(|rhs| lhs * rhs)),
                            &|lhs, constant| lhs.map(|lhs| lhs * constant),
                        )
                        .unwrap_or(0.into());

                    // Here we initialize unassigned cells in a lookup table with 0.
                    // This mimics Halo2's behavior.
                    // https://github.com/zcash/halo2/blob/fed6b000857f27e23ddb07454da8bde4697204f7/halo2_proofs/src/circuit/floor_planner/single_pass.rs#L180

                    ARKWORKS::from_le_bytes_mod_order(&scalar.to_repr())
                })
                .collect()
        })
        .collect();

    let LandT = (0..lookups.len())
        .map(|lookup_index| {
            (
                cell_mapping
                    .iter()
                    .filter_map(|(position, value)| {
                        if position.column_type == VirtualColumnType::LookupInput
                            && position.column_index == lookup_index
                        {
                            if let CCSValue::InsideZ(z_index) = value {
                                Some(z_index)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    })
                    .copied()
                    .collect(),
                tables[lookup_index].clone(),
            )
        })
        .collect();

    println!(
        "The number of advice cells in the original Plonkish table: {}",
        advice.len() * advice[0].len()
    );
    println!(
        "The number of witnesses in the transpiled CCS circuit: {}",
        z.len() - ccs_instance.l
    );

    Ok((ccs_instance, z, LandT))
}
