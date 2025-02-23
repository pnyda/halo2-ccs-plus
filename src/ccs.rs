use crate::monomial::*;
use crate::*;
use ark_std::log2;
use folding_schemes::arith::ccs::CCS;
use folding_schemes::utils::vec::hadamard;
use folding_schemes::utils::vec::mat_vec_mul;
use folding_schemes::utils::vec::SparseMatrix;
use std::collections::HashMap;
use std::collections::HashSet;

// This function generates a M_j matrix for a Query.
// Note that the output of this function does not go into a CCS instance directly,
//   rather it goes through a bunch of transformation in the process.
pub(crate) fn generate_mj<F: ark_ff::PrimeField>(
    query: Query,
    table_height: usize,
    z_height: usize,
    cell_mapping: &HashMap<AbsoluteCellPosition, CCSValue<F>>,
) -> SparseMatrix<F> {
    let mut mj = SparseMatrix::empty();
    mj.n_cols = z_height;
    mj.n_rows = table_height;
    // n_rows will be increased later in the process if there were multiple custom gates.

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
pub(crate) fn generate_naive_ccs_instance<
    HALO2: ff::PrimeField<Repr = [u8; 32]>,
    F: ark_ff::PrimeField,
>(
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
                // M matrix exists for each (gate, query) combination.
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

pub(crate) fn generate_ccs_instance<
    HALO2: ff::PrimeField<Repr = [u8; 32]>,
    F: ark_ff::PrimeField,
>(
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
// Excepts a CCS instance where no M matrix is reused. In other words the same integer does not appear twice in S.
pub(crate) fn reduce_d<F: ark_ff::PrimeField>(ccs: &mut CCS<F>) {
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
pub(crate) fn reduce_t<F: ark_ff::PrimeField>(ccs: &mut CCS<F>) {
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
pub(crate) fn reduce_n<F: ark_ff::PrimeField>(
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

pub(crate) fn generate_z<HALO2: ff::PrimeField<Repr = [u8; 32]>, ARKWORKS: ark_ff::PrimeField>(
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
    // the value at AbsoluteCellPosition with less ordering should take precedence

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
            } else {
                // Check test_generate_z_corner_case to see why this is needed.
                z[z_index] = 0.into();
            }
        }
    }

    z
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_pallas::Fq;
    use folding_schemes::utils::vec::dense_matrix_to_sparse;
    use halo2_proofs::{pasta::Fp, poly::Rotation};

    #[test]
    fn test_generate_mj_advice() {
        let query = Query::Advice(AdviceQuery {
            index: 0,
            column_index: 0,
            rotation: Rotation(0),
        });
        let table_height = 4;
        let z_height = 5;
        let mut cell_mapping: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = HashMap::new();
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(1),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideZ(2),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideZ(3),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 3,
            },
            CCSValue::InsideZ(4),
        );

        let actual = generate_mj(query, table_height, z_height, &cell_mapping);
        let expect: SparseMatrix<Fq> = dense_matrix_to_sparse(vec![
            vec![0.into(), 1.into(), 0.into(), 0.into(), 0.into()],
            vec![0.into(), 0.into(), 1.into(), 0.into(), 0.into()],
            vec![0.into(), 0.into(), 0.into(), 1.into(), 0.into()],
            vec![0.into(), 0.into(), 0.into(), 0.into(), 1.into()],
        ]);
        assert_eq!(actual, expect);
    }

    #[test]
    fn test_generate_mj_advice_rotation() {
        let query = Query::Advice(AdviceQuery {
            index: 0,
            column_index: 0,
            rotation: Rotation(1),
        });
        let table_height = 4;
        let z_height = 5;
        let mut cell_mapping: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = HashMap::new();
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(1),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideZ(2),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideZ(3),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 3,
            },
            CCSValue::InsideZ(4),
        );

        let actual = generate_mj(query, table_height, z_height, &cell_mapping);
        let expect: SparseMatrix<Fq> = dense_matrix_to_sparse(vec![
            vec![0.into(), 0.into(), 1.into(), 0.into(), 0.into()],
            vec![0.into(), 0.into(), 0.into(), 1.into(), 0.into()],
            vec![0.into(), 0.into(), 0.into(), 0.into(), 1.into()],
            vec![0.into(), 1.into(), 0.into(), 0.into(), 0.into()],
        ]);
        assert_eq!(actual, expect);
    }

    #[test]
    fn test_generate_mj_fixed() {
        let query = Query::Fixed(FixedQuery {
            index: 0,
            column_index: 0,
            rotation: Rotation(0),
        });
        let table_height = 4;
        let z_height = 5;
        let mut cell_mapping: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = HashMap::new();
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideM(12.into()),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideM(34.into()),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideM(56.into()),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 3,
            },
            CCSValue::InsideM(78.into()),
        );

        let actual = generate_mj(query, table_height, z_height, &cell_mapping);
        let expect: SparseMatrix<Fq> = dense_matrix_to_sparse(vec![
            vec![12.into(), 0.into(), 0.into(), 0.into(), 0.into()],
            vec![34.into(), 0.into(), 0.into(), 0.into(), 0.into()],
            vec![56.into(), 0.into(), 0.into(), 0.into(), 0.into()],
            vec![78.into(), 0.into(), 0.into(), 0.into(), 0.into()],
        ]);
        assert_eq!(actual, expect);
    }

    #[test]
    fn test_generate_mj_fixed_rotation() {
        let query = Query::Fixed(FixedQuery {
            index: 0,
            column_index: 0,
            rotation: Rotation(-1),
        });
        let table_height = 4;
        let z_height = 5;
        let mut cell_mapping: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = HashMap::new();
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideM(12.into()),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideM(34.into()),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideM(56.into()),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 3,
            },
            CCSValue::InsideM(78.into()),
        );

        let actual = generate_mj(query, table_height, z_height, &cell_mapping);
        let expect: SparseMatrix<Fq> = dense_matrix_to_sparse(vec![
            vec![78.into(), 0.into(), 0.into(), 0.into(), 0.into()],
            vec![12.into(), 0.into(), 0.into(), 0.into(), 0.into()],
            vec![34.into(), 0.into(), 0.into(), 0.into(), 0.into()],
            vec![56.into(), 0.into(), 0.into(), 0.into(), 0.into()],
        ]);
        assert_eq!(actual, expect);
    }

    #[test]
    fn test_reduce_d_mixed() {
        // A circuit with k=1
        // Has one selector column, one fixed column, one instance column, one advice column.
        let subject: CCS<Fq> = CCS {
            m: 2,
            n: 5,
            l: 2,
            t: 4,
            q: 1,
            d: 4,
            s: 2,
            s_prime: 3,
            // Let's say M_0 is generated from Selector query, M_1 is from FixedQuery, M_2 is from InstanceQuery, M_3 is from AdviceQuery
            S: vec![vec![0, 1, 2, 3]],
            c: vec![1.into()],
            M: vec![
                // The selector is turned off at the second row
                dense_matrix_to_sparse(vec![
                    vec![1.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                    vec![0.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                ]),
                // The assignments on the fixed column was [2, 3]
                dense_matrix_to_sparse(vec![
                    vec![2.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                    vec![3.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                ]),
                // Queries the instance column. The second row of the instance column was queried only when the selector is turned off. This means that we should not pack the second row of the instance column into Z.
                dense_matrix_to_sparse(vec![
                    vec![0.into(), 1.into(), 0.into(), 0.into(), 0.into()],
                    vec![0.into(), 0.into(), 1.into(), 0.into(), 0.into()],
                ]),
                // Queries the advice column. The first row of the advice column was queried when the selector is turned off, but it was also queried when the selector was turned on. This means that we should not remove that cell from Z.
                // The second row of the advice column is literally unconstrained.
                dense_matrix_to_sparse(vec![
                    vec![0.into(), 0.into(), 0.into(), 1.into(), 0.into()],
                    vec![0.into(), 0.into(), 0.into(), 1.into(), 0.into()],
                ]),
            ],
        };

        let mut actual = subject.clone();
        reduce_d(&mut actual);

        let mut expect = CCS {
            S: vec![vec![0, 1]],
            M: vec![
                // M_0, M_1, M_2, batched
                dense_matrix_to_sparse(vec![
                    vec![0.into(), 2.into(), 0.into(), 0.into(), 0.into()],
                    vec![0.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                ]),
                // M_3, modified
                dense_matrix_to_sparse(vec![
                    vec![0.into(), 0.into(), 0.into(), 1.into(), 0.into()],
                    vec![0.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                ]),
            ],
            t: 2,
            d: 2,
            ..subject
        };

        // Even when 2 SparseMatrix represents the same matrix, SparseMatrix.equal() returns false when the internal representation of the matrix differs...? We need to sanitize SparseMatrix before calling assert_eq
        for mj in actual.M.iter_mut() {
            *mj = dense_matrix_to_sparse(mj.to_dense());
        }

        for mj in expect.M.iter_mut() {
            *mj = dense_matrix_to_sparse(mj.to_dense());
        }

        assert_eq!(actual, expect);
    }

    #[test]
    fn test_reduce_d_static() {
        let subject: CCS<Fq> = CCS {
            m: 2,
            n: 5,
            l: 2,
            t: 2,
            q: 1,
            d: 2,
            s: 2,
            s_prime: 3,
            // Let's say M_0 is generated from Selector query, M_1 is from FixedQuery
            S: vec![vec![0, 1]],
            c: vec![1.into()],
            M: vec![
                // The selector is turned off at the second row
                dense_matrix_to_sparse(vec![
                    vec![1.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                    vec![0.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                ]),
                // The assignments on the fixed column was [2, 3]
                dense_matrix_to_sparse(vec![
                    vec![2.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                    vec![3.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                ]),
            ],
        };

        let mut actual = subject.clone();
        reduce_d(&mut actual);

        let mut expect = CCS {
            S: vec![vec![0]],
            M: vec![
                // M_0, M_1, batched
                dense_matrix_to_sparse(vec![
                    vec![2.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                    vec![0.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                ]),
            ],
            t: 1,
            d: 1,
            ..subject
        };

        // Even when 2 SparseMatrix represents the same matrix, SparseMatrix.equal() returns false when the internal representation of the matrix differs...? We need to sanitize SparseMatrix before calling assert_eq
        for mj in actual.M.iter_mut() {
            *mj = dense_matrix_to_sparse(mj.to_dense());
        }

        for mj in expect.M.iter_mut() {
            *mj = dense_matrix_to_sparse(mj.to_dense());
        }

        assert_eq!(actual, expect);
    }

    #[test]
    fn test_reduce_d_dynamic() {
        let subject: CCS<Fq> = CCS {
            m: 2,
            n: 5,
            l: 2,
            t: 2,
            q: 1,
            d: 2,
            s: 2,
            s_prime: 3,
            // Let's say M_0 is from InstanceQuery, M_1 is from AdviceQuery
            S: vec![vec![0, 1]],
            c: vec![1.into()],
            M: vec![
                // Queries the instance column.
                dense_matrix_to_sparse(vec![
                    vec![0.into(), 1.into(), 0.into(), 0.into(), 0.into()],
                    vec![0.into(), 0.into(), 1.into(), 0.into(), 0.into()],
                ]),
                // Queries the advice column.
                dense_matrix_to_sparse(vec![
                    vec![0.into(), 0.into(), 0.into(), 1.into(), 0.into()],
                    vec![0.into(), 0.into(), 0.into(), 1.into(), 0.into()],
                ]),
            ],
        };

        let mut actual = subject.clone();
        reduce_d(&mut actual);

        // No change on the CCS instance
        let mut expect = subject.clone();

        // Even when 2 SparseMatrix represents the same matrix, SparseMatrix.equal() returns false when the internal representation of the matrix differs...? We need to sanitize SparseMatrix before calling assert_eq
        for mj in actual.M.iter_mut() {
            *mj = dense_matrix_to_sparse(mj.to_dense());
        }

        for mj in expect.M.iter_mut() {
            *mj = dense_matrix_to_sparse(mj.to_dense());
        }

        assert_eq!(actual, expect);
    }

    #[test]
    fn test_reduce_t() {
        let m0 = dense_matrix_to_sparse(vec![
            vec![1.into(), 0.into(), 0.into(), 0.into(), 0.into()],
            vec![0.into(), 0.into(), 0.into(), 0.into(), 0.into()],
        ]);

        let mut m1 = SparseMatrix::empty();
        m1.n_cols = 5;
        m1.n_rows = 2;
        m1.coeffs.push(vec![(1.into(), 0)]);
        m1.coeffs.push(vec![(0.into(), 0)]);

        let mut m2 = SparseMatrix::empty();
        m2.n_cols = 5;
        m2.n_rows = 2;
        m2.coeffs.push(vec![(1.into(), 0)]);
        m2.coeffs.push(vec![]);

        let subject: CCS<Fq> = CCS {
            m: 2,
            n: 5,
            l: 2,
            t: 3,
            q: 1,
            d: 3,
            s: 2,
            s_prime: 3,
            c: vec![1.into()],
            S: vec![vec![0, 1, 2]],
            M: vec![m0.clone(), m1.clone(), m2.clone()],
        };

        let mut actual = subject.clone();
        reduce_t(&mut actual);

        let expect = CCS {
            S: vec![vec![0, 0, 0]],
            M: vec![m0.clone()],
            t: 1,
            ..subject
        };

        assert_eq!(actual, expect);
    }

    #[test]
    fn test_reduce_n() {
        let ccs: CCS<Fq> = CCS {
            m: 2,
            n: 5,
            l: 2,
            t: 2,
            q: 1,
            d: 2,
            s: 2,
            s_prime: 3,
            c: vec![1.into()],
            S: vec![vec![0, 1]],
            M: vec![
                // M_0, M_1, M_2, batched
                dense_matrix_to_sparse(vec![
                    // z = (1, x, w)
                    //   1         x[0]      x[1]      w[0]      w[1]
                    vec![0.into(), 2.into(), 0.into(), 0.into(), 0.into()],
                    vec![0.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                ]),
                // M_3, modified
                dense_matrix_to_sparse(vec![
                    vec![0.into(), 0.into(), 0.into(), 1.into(), 0.into()],
                    vec![0.into(), 0.into(), 0.into(), 0.into(), 0.into()],
                ]),
            ],
        };
        // This test case is continuation of test_reduce_d_mixed.
        // Z[4] is a literally unconstrained cell, and Z[2] is a virtually unconstrained cell.
        // Both should be removed.

        let mut cell_mapping: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = HashMap::new();
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Selector,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideM(1.into()),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Selector,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideM(0.into()),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideM(2.into()),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideM(3.into()),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(1),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideZ(2),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(3),
        );
        cell_mapping.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideZ(4),
        );

        let mut actual = ccs.clone();
        reduce_n(&mut actual, &mut cell_mapping);

        let expect = CCS {
            M: vec![
                dense_matrix_to_sparse(vec![
                    vec![0.into(), 2.into(), 0.into()],
                    vec![0.into(), 0.into(), 0.into()],
                ]),
                dense_matrix_to_sparse(vec![
                    vec![0.into(), 0.into(), 1.into()],
                    vec![0.into(), 0.into(), 0.into()],
                ]),
            ],
            n: 3,
            l: 1,
            ..ccs
        };

        assert_eq!(actual, expect);
    }

    #[test]
    fn test_generate_z_corner_case() {
        let mut cell_mapping: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = HashMap::new();
        cell_mapping.insert(
            // cell A
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(1),
        );
        cell_mapping.insert(
            // cell B
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideZ(1),
        );
        // There is a copy constraint between cell A and cell B.

        // AbsoluteCellPosition A < AbsoluteCellPosition B
        // so the value assigned at the cell A should decide the value assigned at Z[1].

        // but the cell A in the original table is unassigned.
        let advice: [[Option<Fp>; 2]; 1] = [[None, Some(2.into())]];
        let selectors = Vec::new();
        let fixed = Vec::new();
        let instance = Vec::new();

        let z = generate_z(
            &selectors,
            &fixed,
            &instance,
            &advice.each_ref().map(|x| &x[..]),
            &cell_mapping,
            &[],
        );

        // Halo 2 initializes Cell A with 0, so I think we should follow that behavior.
        // Maybe it doesn't matter
        assert_eq!(z, vec![1.into(), 0.into()]);
    }
}
