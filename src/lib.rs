#![allow(non_snake_case)]
use ark_std::log2;
use folding_schemes::arith::ccs::CCS;
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

#[derive(Debug, Clone, Copy)]
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

    for (column_index, column) in instance.into_iter().enumerate() {
        for (row_index, _) in column.into_iter().enumerate() {
            let z_index = 1 + cell_mapping.len();
            let cell_position = AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index,
                row_index,
            };
            cell_mapping.insert(cell_position, CCSValue::InsideZ(z_index));
        }
    }

    for (column_index, column) in advice.into_iter().enumerate() {
        for (row_index, _) in column.into_iter().enumerate() {
            let z_index = 1 + cell_mapping.len();
            let cell_position = AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index,
                row_index,
            };
            cell_mapping.insert(cell_position, CCSValue::InsideZ(z_index));
        }
    }

    for (column_index, column) in fixed.into_iter().enumerate() {
        for (row_index, cell) in column.into_iter().enumerate() {
            // TODO: Is it okay to initialize unassigned fixed cell with 0?
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
    let mut z_height = clean_unused_z(&mut cell_mapping);

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
    let mut copy_constraints_sorted: Vec<(AbsoluteCellPosition, AbsoluteCellPosition)> =
        copy_constraints
            .iter()
            .filter_map(|copy_constraint| {
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

                // The first element of the tuple gets deduplicated into the second element of the tuple
                match cell1.cmp(&cell2) {
                    Ordering::Equal => None,
                    Ordering::Less => Some((cell1, cell2)),
                    Ordering::Greater => Some((cell2, cell1)),
                }
            })
            .collect();

    // When there are copy constraints that states
    // B = C
    // B = A
    // cell_mapping[C] should be z_index of A.
    // We achieve this by sorting the copy constraints
    // A <- B
    // B <- C
    // and applying witness deduplication for AbsoluteCellPosition with less ordering first
    copy_constraints_sorted.sort();

    for (deduplicate_into, deduplicate_from) in copy_constraints_sorted.into_iter() {
        *cell_mapping.get_mut(&deduplicate_from).unwrap() =
            cell_mapping.get(&deduplicate_into).copied().unwrap();
    }
}

// The witness deduplication will make some z_index unused
// Thus we have to reassign all z_index, to skip unused indexes
// Returns the height of Z vector after the clean up
fn clean_unused_z<F: ark_ff::PrimeField>(
    cell_mapping: &mut HashMap<AbsoluteCellPosition, CCSValue<F>>,
) -> usize {
    let mut used_z_index: Vec<&mut usize> = cell_mapping
        .values_mut()
        .filter_map(|ccs_value| match ccs_value {
            CCSValue::InsideM(_) => None,
            CCSValue::InsideZ(z_index) => Some(z_index),
        })
        .collect();

    // HashMap.values_mut() returns an iterator with undefined order.
    // So we have to sort it here.
    used_z_index.sort();

    let mut z_height = 1;
    let mut last_z_index = 0;
    for z_index in used_z_index.into_iter() {
        if *z_index == last_z_index {
            // If z_index didn't change, we don't increase z_height
            *z_index = z_height - 1;
        } else {
            // If z_index change, we increase z_height
            last_z_index = *z_index;
            *z_index = z_height;
            z_height += 1;
        }
    }

    z_height
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

fn generate_ccs_instance<HALO2: ff::PrimeField<Repr = [u8; 32]>, F: ark_ff::PrimeField>(
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

    // A map from (custom gate ID, queried column type, queried column index, rotation) -> M_j
    let mut m_map: HashMap<(usize, Query), SparseMatrix<F>> = HashMap::new();
    for (gate_index, monomials) in gates.iter().enumerate() {
        for monomial in monomials.iter() {
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

                m_map.insert((gate_index, *query), mj);
            }
        }
    }
    let m_pair: Vec<((usize, Query), SparseMatrix<F>)> = m_map.into_iter().collect();

    let c: Vec<F> = gates
        .iter()
        .flat_map(|monomials| monomials.iter().map(|monomial| monomial.coefficient))
        .collect();
    let S: Vec<Vec<usize>> = gates
        .iter()
        .enumerate()
        .flat_map(|(gate_index1, monomials)| {
            monomials
                .iter()
                .map(|monomial| {
                    monomial
                        .variables
                        .iter()
                        .map(|query1| {
                            let j = m_pair
                                .iter()
                                .position(|((gate_index2, query2), _)| {
                                    gate_index1 == *gate_index2 && query1 == query2
                                })
                                .unwrap();
                            j
                        })
                        .collect()
                })
                .collect::<Vec<_>>()
        })
        .collect();
    let M: Vec<SparseMatrix<F>> = m_pair.into_iter().map(|(_, mat)| mat).collect();

    CCS {
        m,
        n: z_height,
        l: num_instance_cells,
        t: M.len(),
        q: S.len(),
        d: S.iter().map(|multiset| multiset.len()).max().unwrap_or(1),
        s: log2(table_height) as usize,
        s_prime: log2(z_height) as usize,
        M: M,
        S: S,
        c: c,
    }
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

    // Unassigned cell in the original Plonkish table will be initialized with 0.
    // TODO: Is this an appropriate behavior? Should I randomize it?
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
    let instance_option: Vec<&[Option<HALO2>]> = instance_option
        .iter()
        .map(|x| x.as_slice())
        .collect::<Vec<_>>();
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

    let lookups = dump_lookups::<HALO2, C>()?;
    let lookup_inputs: Vec<Expression<HALO2>> =
        lookups.iter().map(|(input, _)| input).cloned().collect();
    let cell_mapping = generate_cell_mapping(
        &instance_option,
        &advice,
        &fixed,
        &selectors,
        &cell_dumper.copy_constraints,
        &lookup_inputs,
    );

    let custom_gates = dump_gates::<HALO2, C>()?;
    let ccs_instance: CCS<ARKWORKS> =
        generate_ccs_instance(&custom_gates, &cell_mapping, &lookup_inputs);
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
                    // TODO: Is it ok to initialize unassigned cell in a lookup table with 0?
                    ARKWORKS::from_le_bytes_mod_order(&scalar.to_repr())
                })
                .collect()
        })
        .collect();

    let L = (0..lookups.len())
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

    Ok((ccs_instance, z, L))
}
