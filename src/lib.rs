#![allow(non_snake_case)]
use ark_std::log2;
use folding_schemes::arith::ccs::CCS;
use folding_schemes::utils::vec::SparseMatrix;
use halo2_proofs::dump::CopyConstraint;
use halo2_proofs::plonk::*;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

#[derive(Debug, Clone, Copy)]
enum Query {
    Fixed(FixedQuery),
    Advice(AdviceQuery),
    Instance(InstanceQuery),
    Selector(Selector),
}

impl Hash for Query {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        // Ignore query_index and care only about the cell position

        match self {
            Self::Fixed(query) => {
                hasher.write(&[0u8]); // enum variant ID
                hasher.write(&query.rotation.0.to_le_bytes());
                hasher.write(&query.column_index.to_le_bytes());
            }
            Self::Advice(query) => {
                hasher.write(&[1u8]); // enum variant ID
                hasher.write(&query.rotation.0.to_le_bytes());
                hasher.write(&query.column_index.to_le_bytes());
            }
            Self::Instance(query) => {
                hasher.write(&[2u8]); // enum variant ID
                hasher.write(&query.rotation.0.to_le_bytes());
                hasher.write(&query.column_index.to_le_bytes());
            }
            Self::Selector(query) => {
                hasher.write(&[3u8]); // enum variant ID
                hasher.write(&query.0.to_le_bytes());
            }
        }

        hasher.finish();
    }
}

impl PartialEq for Query {
    fn eq(&self, other: &Self) -> bool {
        // Ignore query_index and care only about the cell position

        match (self, other) {
            (Self::Fixed(lhs), Self::Fixed(rhs)) => {
                lhs.rotation == rhs.rotation && lhs.column_index == rhs.column_index
            }
            (Self::Advice(lhs), Self::Advice(rhs)) => {
                lhs.rotation == rhs.rotation && lhs.column_index == rhs.column_index
            }
            (Self::Instance(lhs), Self::Instance(rhs)) => {
                lhs.rotation == rhs.rotation && lhs.column_index == rhs.column_index
            }
            (Self::Selector(lhs), Self::Selector(rhs)) => lhs.0 == rhs.0,
            _ => false,
        }
    }
}

impl Eq for Query {}

#[derive(Debug)]
struct Monomial<F: ark_ff::PrimeField> {
    coefficient: F,
    variables: Vec<Query>,
}

fn get_monomials<HALO2: ff::PrimeField<Repr = [u8; 32]>, ARKWORKS: ark_ff::PrimeField>(
    expr: Expression<HALO2>,
) -> Vec<Monomial<ARKWORKS>> {
    match expr {
        Expression::Constant(constant) => vec![Monomial {
            coefficient: ARKWORKS::from_le_bytes_mod_order(&constant.to_repr()),
            variables: vec![],
        }],
        Expression::Selector(query) => vec![Monomial {
            coefficient: 1.into(),
            variables: vec![Query::Selector(query)],
        }],
        Expression::Advice(query) => vec![Monomial {
            coefficient: 1.into(),
            variables: vec![Query::Advice(query)],
        }],
        Expression::Fixed(query) => vec![Monomial {
            coefficient: 1.into(),
            variables: vec![Query::Fixed(query)],
        }],
        Expression::Instance(query) => vec![Monomial {
            coefficient: 1.into(),
            variables: vec![Query::Instance(query)],
        }],
        Expression::Negated(expr) => get_monomials::<HALO2, ARKWORKS>(*expr)
            .into_iter()
            .map(|original| Monomial {
                coefficient: original.coefficient.neg(),
                variables: original.variables,
            })
            .collect(),
        Expression::Scaled(expr, scalar) => get_monomials::<HALO2, ARKWORKS>(*expr)
            .into_iter()
            .map(|original| Monomial {
                coefficient: original.coefficient
                    * ARKWORKS::from_le_bytes_mod_order(&scalar.to_repr()),
                variables: original.variables,
            })
            .collect(),
        Expression::Sum(lhs, rhs) => {
            let mut result = Vec::new();
            result.extend(get_monomials::<HALO2, ARKWORKS>(*lhs));
            result.extend(get_monomials::<HALO2, ARKWORKS>(*rhs));
            result
        }
        Expression::Product(lhs, rhs) => {
            let lhs_monomials = get_monomials::<HALO2, ARKWORKS>(*lhs);
            let rhs_monomials = get_monomials::<HALO2, ARKWORKS>(*rhs);
            let mut result = Vec::new();

            for lhs_monomial in lhs_monomials.iter() {
                for rhs_monomial in rhs_monomials.iter() {
                    let mut variables = Vec::new();
                    variables.extend(lhs_monomial.variables.iter().copied());
                    variables.extend(rhs_monomial.variables.iter().copied());

                    result.push(Monomial {
                        coefficient: lhs_monomial.coefficient * rhs_monomial.coefficient,
                        variables,
                    })
                }
            }

            result
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum CCSValue<F: ark_ff::PrimeField> {
    InsideZ(usize), // z_index
    InsideM(F),     // fixed value
}

// A mapping from absolute cell position in the original table (column_type, column_index, row_index)
// to the position in Z
fn generate_cell_mapping<HALO2: ff::PrimeField<Repr = [u8; 32]>, ARKWORKS: ark_ff::PrimeField>(
    instance: &[&[Option<HALO2>]],
    advice: &[&[Option<HALO2>]],
    fixed: &[&[Option<HALO2>]],
    selectors: &[&[bool]],
    copy_constraints: &[CopyConstraint],
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
    clean_unused_z(&mut cell_mapping);

    cell_mapping
}

// I use this Ord impl for witness deduplication.
// Cells with greater ordering will get deduplicated into cells with less ordering.
// If there was a copy constraint between an advice cell and an instance cell,
//   the former will get deduplicated into the latter.
// If there was a copy constraint between an advice cell and a fixed cell,
//   the former will get deduplicated into the latter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum VirtualColumnType {
    Selector,
    Fixed,
    Instance,
    Advice,
}

impl From<Any> for VirtualColumnType {
    fn from(value: Any) -> Self {
        match value {
            Any::Instance => VirtualColumnType::Instance,
            Any::Advice => VirtualColumnType::Advice,
            Any::Fixed => VirtualColumnType::Fixed,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct AbsoluteCellPosition {
    column_type: VirtualColumnType,
    column_index: usize,
    row_index: usize,
}

// I use this Ord impl for witness deduplication.
// Cells with greater ordering will get deduplicated into cells with less ordering.
impl Ord for AbsoluteCellPosition {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.column_type.cmp(&other.column_type) {
            Ordering::Equal => match self.column_index.cmp(&other.column_index) {
                Ordering::Equal => self.row_index.cmp(&other.row_index),
                ordering => ordering,
            },
            ordering => ordering,
        }
    }
}

impl PartialOrd for AbsoluteCellPosition {
    fn partial_cmp(&self, other: &AbsoluteCellPosition) -> Option<Ordering> {
        Some(self.cmp(other))
    }
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
// Thus we have to reassign z_index
fn clean_unused_z<F: ark_ff::PrimeField>(
    cell_mapping: &mut HashMap<AbsoluteCellPosition, CCSValue<F>>,
) {
    let mut used_z_index: Vec<&mut usize> = cell_mapping
        .values_mut()
        .filter_map(|ccs_value| match ccs_value {
            CCSValue::InsideM(_) => None,
            CCSValue::InsideZ(z_index) => Some(z_index),
        })
        .collect();
    used_z_index.sort();

    let mut z_height = 1;
    let mut last_z_index = 0;
    for z_index in used_z_index.into_iter() {
        if *z_index == last_z_index {
            *z_index = z_height - 1;
        } else {
            last_z_index = *z_index;
            *z_index = z_height;
            z_height += 1;
        }
    }
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
        let cell_position = match query {
            Query::Selector(query) => AbsoluteCellPosition {
                column_type: VirtualColumnType::Selector,
                column_index: query.0,
                row_index: y,
            },
            Query::Fixed(query) => AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: query.column_index,
                row_index: (y as i32 + query.rotation.0).rem_euclid(table_height as i32) as usize,
            },
            Query::Instance(query) => AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index: query.column_index,
                row_index: (y as i32 + query.rotation.0).rem_euclid(table_height as i32) as usize,
            },
            Query::Advice(query) => AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: query.column_index,
                row_index: (y as i32 + query.rotation.0).rem_euclid(table_height as i32) as usize,
            },
        };

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

// Right now it only supports single custom gate
// TODO: Support multiple custom gates
fn generate_ccs_instance<F: ark_ff::PrimeField>(
    custom_gates: &[&[Monomial<F>]],
    cell_mapping: &HashMap<AbsoluteCellPosition, CCSValue<F>>,
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

    let m = custom_gates.len() * table_height;

    // A map from (custom gate ID, queried column type, queried column index, rotation) -> M_j
    let mut m_map: HashMap<(usize, Query), SparseMatrix<F>> = HashMap::new();
    for (gate_index, monomials) in custom_gates.iter().enumerate() {
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

    let c: Vec<F> = custom_gates
        .iter()
        .flat_map(|monomials| monomials.iter().map(|monomial| monomial.coefficient))
        .collect();
    let S: Vec<Vec<usize>> = custom_gates
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
    instance: &[&[Option<HALO2>]],
    advice: &[&[Option<HALO2>]],
    cell_mapping: &HashMap<AbsoluteCellPosition, CCSValue<ARKWORKS>>,
) -> Vec<ARKWORKS> {
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

    for cell_position in cells {
        let cell_value = match cell_position.column_type {
            VirtualColumnType::Advice => {
                advice[cell_position.column_index][cell_position.row_index]
            }
            VirtualColumnType::Instance => {
                instance[cell_position.column_index][cell_position.row_index]
            }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::primitives::P128Pow5T3 as OrchardNullifier;
    use ark_pallas::Fq;
    use ark_std::rand::rngs::OsRng;
    use ff::Field;
    use folding_schemes::utils::vec::is_zero_vec;
    use halo2_gadgets::poseidon::primitives::*;
    use halo2_gadgets::poseidon::*;
    use halo2_proofs::circuit::AssignedCell;
    use halo2_proofs::circuit::Layouter;
    use halo2_proofs::circuit::SimpleFloorPlanner;
    use halo2_proofs::circuit::Value;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::dump::{dump_gates, dump_lookups, AssignmentDumper};
    use halo2_proofs::pasta::Fp;
    use halo2_proofs::plonk::Error;
    use halo2_proofs::poly::Rotation;
    use std::marker::PhantomData;

    #[test]
    fn test_fibonacci_satisfiability() -> Result<(), Error> {
        let custom_gates = dump_gates::<Fp, FibonacciCircuit<Fp>>()?;
        let monomials: Vec<Vec<Monomial<Fq>>> = custom_gates
            .into_iter()
            .map(|expr| get_monomials(expr))
            .collect();
        let monomials: Vec<&[Monomial<Fq>]> = monomials.iter().map(|x| x.as_slice()).collect();

        let k = 4;
        let mut meta = ConstraintSystem::<Fp>::default();
        let config = FibonacciCircuit::configure(&mut meta);

        let mut instance_column: Vec<Option<Fp>> = vec![None; 1 << k];
        instance_column[0] = Some(1.into());
        instance_column[1] = Some(1.into());
        instance_column[2] = Some(55.into());

        let mut cell_dumper: AssignmentDumper<Fp> = AssignmentDumper::new(k, &meta);
        cell_dumper.instance[0][0] = Value::known(instance_column[0].unwrap());
        cell_dumper.instance[0][1] = Value::known(instance_column[1].unwrap());
        cell_dumper.instance[0][2] = Value::known(instance_column[2].unwrap());

        let circuit = FibonacciCircuit(PhantomData);
        <<FibonacciCircuit<Fp> as Circuit<Fp>>::FloorPlanner as FloorPlanner>::synthesize(
            &mut cell_dumper,
            &circuit,
            config,
            meta.constants.clone(),
        )?;

        let advice: Vec<&[Option<Fp>]> = cell_dumper
            .advice
            .iter()
            .map(|x| x.as_slice())
            .collect::<Vec<_>>();
        let fixed: Vec<&[Option<Fp>]> = cell_dumper
            .fixed
            .iter()
            .map(|x| x.as_slice())
            .collect::<Vec<_>>();
        let selectors: Vec<&[bool]> = cell_dumper
            .selectors
            .iter()
            .map(|x| x.as_slice())
            .collect::<Vec<_>>();

        let cell_mapping = generate_cell_mapping(
            &[&instance_column],
            &advice,
            &fixed,
            &selectors,
            &cell_dumper.copy_constraints,
        );
        let ccs_instance: CCS<ark_pallas::Fq> = generate_ccs_instance(&monomials, &cell_mapping);
        let z: Vec<ark_pallas::Fq> = generate_z(&[&instance_column], &advice, &cell_mapping);

        assert!(is_zero_vec(&ccs_instance.eval_at_z(&z).unwrap()));

        Ok(())
    }

    #[test]
    fn test_fibonacci_unsatisfied() -> Result<(), Error> {
        let custom_gates = dump_gates::<Fp, FibonacciCircuit<Fp>>()?;
        let monomials: Vec<Vec<Monomial<Fq>>> = custom_gates
            .into_iter()
            .map(|expr| get_monomials(expr))
            .collect();
        let monomials: Vec<&[Monomial<Fq>]> = monomials.iter().map(|x| x.as_slice()).collect();

        let k = 4;
        let mut meta = ConstraintSystem::<Fp>::default();
        let config = FibonacciCircuit::configure(&mut meta);

        let mut instance_column: Vec<Option<Fp>> = vec![None; 1 << k];
        instance_column[0] = Some(1.into());
        instance_column[1] = Some(1.into());
        instance_column[2] = Some(54.into());

        let mut cell_dumper: AssignmentDumper<Fp> = AssignmentDumper::new(k, &meta);
        cell_dumper.instance[0][0] = Value::known(instance_column[0].unwrap());
        cell_dumper.instance[0][1] = Value::known(instance_column[1].unwrap());
        cell_dumper.instance[0][2] = Value::known(instance_column[2].unwrap());

        let circuit = FibonacciCircuit(PhantomData);
        <<FibonacciCircuit<Fp> as Circuit<Fp>>::FloorPlanner as FloorPlanner>::synthesize(
            &mut cell_dumper,
            &circuit,
            config,
            meta.constants.clone(),
        )?;

        let advice: Vec<&[Option<Fp>]> = cell_dumper
            .advice
            .iter()
            .map(|x| x.as_slice())
            .collect::<Vec<_>>();
        let fixed: Vec<&[Option<Fp>]> = cell_dumper
            .fixed
            .iter()
            .map(|x| x.as_slice())
            .collect::<Vec<_>>();
        let selectors: Vec<&[bool]> = cell_dumper
            .selectors
            .iter()
            .map(|x| x.as_slice())
            .collect::<Vec<_>>();

        let cell_mapping = generate_cell_mapping(
            &[&instance_column],
            &advice,
            &fixed,
            &selectors,
            &cell_dumper.copy_constraints,
        );
        let ccs_instance: CCS<ark_pallas::Fq> = generate_ccs_instance(&monomials, &cell_mapping);
        let z: Vec<ark_pallas::Fq> = generate_z(&[&instance_column], &advice, &cell_mapping);

        assert!(!is_zero_vec(&ccs_instance.eval_at_z(&z).unwrap()));

        Ok(())
    }

    #[test]
    fn test_poseidon_success() -> Result<(), Error> {
        let message = [Fp::random(OsRng), Fp::random(OsRng)];
        let output = halo2_gadgets::poseidon::primitives::Hash::<
            _,
            OrchardNullifier,
            ConstantLength<2>,
            3,
            2,
        >::init()
        .hash(message);

        let k = 6;
        let mut instance_column: Vec<Option<Fp>> = vec![None; 1 << k];
        instance_column[0] = Some(output);

        let circuit = HashCircuit::<OrchardNullifier, 3, 2, 2> {
            message: Value::known(message),
            _spec: PhantomData,
        };

        let mut meta = ConstraintSystem::<Fp>::default();
        let config = HashCircuit::<OrchardNullifier, 3, 2, 2>::configure(&mut meta);
        let mut cell_dumper: AssignmentDumper<Fp> = AssignmentDumper::new(k, &meta);
        cell_dumper.instance[0][0] = Value::known(instance_column[0].unwrap());

        <<HashCircuit<OrchardNullifier, 3, 2, 2> as halo2_proofs::plonk::Circuit<Fp>>::FloorPlanner as FloorPlanner>::synthesize(
            &mut cell_dumper,
            &circuit,
            config,
            meta.constants.clone(),
        )?;

        let advice: Vec<&[Option<Fp>]> = cell_dumper
            .advice
            .iter()
            .map(|x| x.as_slice())
            .collect::<Vec<_>>();
        let fixed: Vec<&[Option<Fp>]> = cell_dumper
            .fixed
            .iter()
            .map(|x| x.as_slice())
            .collect::<Vec<_>>();
        let selectors: Vec<&[bool]> = cell_dumper
            .selectors
            .iter()
            .map(|x| x.as_slice())
            .collect::<Vec<_>>();
        let cell_mapping = generate_cell_mapping(
            &[&instance_column],
            &advice,
            &fixed,
            &selectors,
            &cell_dumper.copy_constraints,
        );

        let custom_gates = dump_gates::<Fp, HashCircuit<OrchardNullifier, 3, 2, 2>>()?;
        let monomials: Vec<Vec<Monomial<Fq>>> = custom_gates
            .into_iter()
            .map(|expr| get_monomials(expr))
            .collect();
        let monomials: Vec<&[Monomial<Fq>]> = monomials.iter().map(|x| x.as_slice()).collect();
        let ccs_instance: CCS<Fq> = generate_ccs_instance(&monomials, &cell_mapping);

        let z: Vec<Fq> = generate_z(&[&instance_column], &advice, &cell_mapping);

        let prover = MockProver::run(k, &circuit, vec![vec![output]]).unwrap();
        assert_eq!(prover.verify(), Ok(()));

        assert!(is_zero_vec(&ccs_instance.eval_at_z(&z).unwrap()));

        Ok(())
    }

    #[test]
    fn test_monomials() -> Result<(), Error> {
        let custom_gates = dump_gates::<Fp, FibonacciCircuit<Fp>>()?;
        dbg!(&custom_gates);

        let monomials: Vec<Vec<Monomial<Fq>>> = custom_gates
            .into_iter()
            .map(|expr| get_monomials(expr))
            .collect();
        dbg!(monomials);

        let k = 4;
        let mut meta = ConstraintSystem::<Fp>::default();
        let config = FibonacciCircuit::configure(&mut meta);

        let mut cell_dumper: AssignmentDumper<Fp> = AssignmentDumper::new(k, &meta);
        cell_dumper.instance[0][0] = Value::known(1.into());
        cell_dumper.instance[0][1] = Value::known(1.into());
        cell_dumper.instance[0][2] = Value::known(55.into());

        let circuit = FibonacciCircuit(PhantomData);
        <<FibonacciCircuit<Fp> as Circuit<Fp>>::FloorPlanner as FloorPlanner>::synthesize(
            &mut cell_dumper,
            &circuit,
            config,
            meta.constants.clone(),
        )?;

        dbg!(cell_dumper);
        dbg!(dump_gates::<Fp, FibonacciCircuit<Fp>>());
        dbg!(dump_lookups::<Fp, FibonacciCircuit<Fp>>());

        Ok(())
    }

    // Taken from https://github.com/icemelon/halo2-examples/blob/master/src/fibonacci/example2.rs

    #[derive(Debug, Clone)]
    struct FibonacciConfig {
        advice: Column<Advice>,
        selector: Selector,
        instance: Column<Instance>,
    }

    #[derive(Debug, Clone)]
    struct FibonacciChip<F: Field> {
        config: FibonacciConfig,
        _marker: PhantomData<F>,
    }

    impl<F: Field> FibonacciChip<F> {
        pub fn construct(config: FibonacciConfig) -> Self {
            Self {
                config,
                _marker: PhantomData,
            }
        }

        pub fn configure(
            meta: &mut ConstraintSystem<F>,
            advice: Column<Advice>,
            instance: Column<Instance>,
        ) -> FibonacciConfig {
            let selector = meta.selector();

            meta.enable_equality(advice);
            meta.enable_equality(instance);

            meta.create_gate("add", |meta| {
                //
                // advice | selector
                //   a    |   s
                //   b    |
                //   c    |
                //
                let s = meta.query_selector(selector);
                let a = meta.query_advice(advice, Rotation::cur());
                let b = meta.query_advice(advice, Rotation::next());
                let c = meta.query_advice(advice, Rotation(2));

                vec![s * (a + b - c)]
            });

            FibonacciConfig {
                advice,
                selector,
                instance,
            }
        }

        pub fn assign(
            &self,
            mut layouter: impl Layouter<F>,
            nrows: usize,
        ) -> Result<AssignedCell<F, F>, Error> {
            layouter.assign_region(
                || "entire fibonacci table",
                |mut region| {
                    self.config.selector.enable(&mut region, 0)?;
                    self.config.selector.enable(&mut region, 1)?;

                    let mut a_cell = region.assign_advice_from_instance(
                        || "1",
                        self.config.instance,
                        0,
                        self.config.advice,
                        0,
                    )?;
                    let mut b_cell = region.assign_advice_from_instance(
                        || "1",
                        self.config.instance,
                        1,
                        self.config.advice,
                        1,
                    )?;

                    for row in 2..nrows {
                        if row < nrows - 2 {
                            self.config.selector.enable(&mut region, row)?;
                        }

                        let c_cell = region.assign_advice(
                            || "advice",
                            self.config.advice,
                            row,
                            || a_cell.value().copied() + b_cell.value(),
                        )?;

                        a_cell = b_cell;
                        b_cell = c_cell;
                    }

                    Ok(b_cell)
                },
            )
        }

        pub fn expose_public(
            &self,
            mut layouter: impl Layouter<F>,
            cell: AssignedCell<F, F>,
            row: usize,
        ) -> Result<(), Error> {
            layouter.constrain_instance(cell.cell(), self.config.instance, row)
        }
    }

    #[derive(Default)]
    struct FibonacciCircuit<F>(PhantomData<F>);

    impl<F: Field> Circuit<F> for FibonacciCircuit<F> {
        type Config = FibonacciConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = meta.advice_column();
            let instance = meta.instance_column();
            FibonacciChip::configure(meta, advice, instance)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = FibonacciChip::construct(config);

            let out_cell = chip.assign(layouter.namespace(|| "entire table"), 10)?;

            chip.expose_public(layouter.namespace(|| "out"), out_cell, 2)?;

            Ok(())
        }
    }

    #[derive(Clone)]
    struct HashConfig<const WIDTH: usize, const RATE: usize> {
        pow5: Pow5Config<Fp, WIDTH, RATE>,
        instance_column: Column<Instance>,
    }

    // Taken from https://github.com/zcash/halo2/blob/halo2_proofs-0.3.0/halo2_gadgets/src/poseidon/pow5.rs#L719
    struct HashCircuit<
        S: Spec<Fp, WIDTH, RATE>,
        const WIDTH: usize,
        const RATE: usize,
        const L: usize,
    > {
        message: Value<[Fp; L]>,
        _spec: PhantomData<S>,
    }

    impl<S: Spec<Fp, WIDTH, RATE>, const WIDTH: usize, const RATE: usize, const L: usize>
        Circuit<Fp> for HashCircuit<S, WIDTH, RATE, L>
    {
        type Config = HashConfig<WIDTH, RATE>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                message: Value::unknown(),
                _spec: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            let state = (0..WIDTH).map(|_| meta.advice_column()).collect::<Vec<_>>();
            let partial_sbox = meta.advice_column();

            let rc_a = (0..WIDTH).map(|_| meta.fixed_column()).collect::<Vec<_>>();
            let rc_b = (0..WIDTH).map(|_| meta.fixed_column()).collect::<Vec<_>>();

            meta.enable_constant(rc_b[0]);

            let pow5 = Pow5Chip::configure::<S>(
                meta,
                state.try_into().unwrap(),
                partial_sbox,
                rc_a.try_into().unwrap(),
                rc_b.try_into().unwrap(),
            );

            let instance_column = meta.instance_column();
            meta.enable_equality(instance_column);

            Self::Config {
                pow5,
                instance_column,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            let chip = Pow5Chip::construct(config.pow5.clone());

            let message = layouter.assign_region(
                || "load message",
                |mut region| {
                    let message_word = |i: usize| {
                        let value = self.message.map(|message_vals| message_vals[i]);
                        region.assign_advice(
                            || format!("load message_{}", i),
                            config.pow5.state[i],
                            0,
                            || value,
                        )
                    };

                    let message: Result<Vec<_>, Error> = (0..L).map(message_word).collect();
                    Ok(message?.try_into().unwrap())
                },
            )?;

            let hasher =
                halo2_gadgets::poseidon::Hash::<_, _, S, ConstantLength<L>, WIDTH, RATE>::init(
                    chip,
                    layouter.namespace(|| "init"),
                )?;
            let output = hasher.hash(layouter.namespace(|| "hash"), message)?;

            layouter.constrain_instance(output.cell(), config.instance_column, 0)
        }
    }
}
