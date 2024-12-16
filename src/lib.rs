// Taken from https://github.com/icemelon/halo2-examples/blob/master/src/fibonacci/example2.rs

use ark_ff::PrimeField;
use ff::PrimeField as _;
use folding_schemes::arith::ccs::CCS;
use folding_schemes::utils::vec::SparseMatrix;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::dump::{dump_gates, dump_lookups, AssignmentDumper, CopyConstraint};
use halo2_proofs::pasta::Fp;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::marker::PhantomData;

#[test]
fn test_monomials() -> Result<(), Error> {
    let custom_gates = dump_gates::<Fp, MyCircuit<Fp>>()?;
    dbg!(&custom_gates);

    let monomials: Vec<Vec<Monomial<Fp>>> = custom_gates
        .into_iter()
        .map(|expr| get_monomials(expr))
        .collect();
    dbg!(monomials);

    let k = 4;
    let mut meta = ConstraintSystem::<Fp>::default();
    let config = MyCircuit::configure(&mut meta);

    let mut cell_dumper: AssignmentDumper<Fp> = AssignmentDumper::new(k, &meta);
    cell_dumper.instance[0][0] = Value::known(1.into());
    cell_dumper.instance[0][1] = Value::known(1.into());
    cell_dumper.instance[0][2] = Value::known(55.into());

    let circuit = MyCircuit(PhantomData);
    <<MyCircuit<Fp> as Circuit<Fp>>::FloorPlanner as FloorPlanner>::synthesize(
        &mut cell_dumper,
        &circuit,
        config,
        meta.constants.clone(),
    )?;

    dbg!(cell_dumper);
    dbg!(dump_gates::<Fp, MyCircuit<Fp>>());
    dbg!(dump_lookups::<Fp, MyCircuit<Fp>>());

    // let ccs = CCS {
    //     M: generate_m(monomials, constant_columns)
    // };

    Ok(())
}

#[derive(Debug, Clone, Copy)]
enum Query {
    Fixed(FixedQuery),
    Advice(AdviceQuery),
    Instance(InstanceQuery),
    Selector(Selector),
}

#[derive(Debug)]
struct Monomial<F: Field> {
    coefficient: F,
    variables: Vec<Query>,
}

fn get_monomials<F: Field>(expr: Expression<F>) -> Vec<Monomial<F>> {
    match expr {
        Expression::Constant(constant) => vec![Monomial {
            coefficient: constant,
            variables: vec![],
        }],
        Expression::Selector(query) => vec![Monomial {
            coefficient: F::ONE,
            variables: vec![Query::Selector(query)],
        }],
        Expression::Advice(query) => vec![Monomial {
            coefficient: F::ONE,
            variables: vec![Query::Advice(query)],
        }],
        Expression::Fixed(query) => vec![Monomial {
            coefficient: F::ONE,
            variables: vec![Query::Fixed(query)],
        }],
        Expression::Instance(query) => vec![Monomial {
            coefficient: F::ONE,
            variables: vec![Query::Instance(query)],
        }],
        Expression::Negated(expr) => get_monomials(*expr)
            .into_iter()
            .map(|original| Monomial {
                coefficient: original.coefficient.neg(),
                variables: original.variables,
            })
            .collect(),
        Expression::Scaled(expr, scalar) => get_monomials(*expr)
            .into_iter()
            .map(|original| Monomial {
                coefficient: original.coefficient * scalar,
                variables: original.variables,
            })
            .collect(),
        Expression::Sum(lhs, rhs) => {
            let mut result = Vec::new();
            result.extend(get_monomials(*lhs));
            result.extend(get_monomials(*rhs));
            result
        }
        Expression::Product(lhs, rhs) => {
            let lhs_monomials = get_monomials(*lhs);
            let rhs_monomials = get_monomials(*rhs);
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

#[derive(Debug, Clone)]
struct FibonacciConfig {
    advice: Column<Advice>,
    selector: Selector,
    instance: Column<Instance>,
    lookup_table: TableColumn,
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
        let lookup_table = meta.lookup_table_column();

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

        meta.lookup(|query| {
            let every_advice_cell = query.query_advice(advice, Rotation::cur());
            vec![(every_advice_cell, lookup_table)]
        });

        FibonacciConfig {
            advice,
            selector,
            instance,
            lookup_table,
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
struct MyCircuit<F>(PhantomData<F>);

impl<F: Field> Circuit<F> for MyCircuit<F> {
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

#[derive(Debug, Clone, Copy)]
enum CCSValue {
    InsideZ(usize), // z_index
    InsideM(Fp),    // fixed value
                    // TODO: Support generic field
                    // TODO: Use arkworks::Field instead of halo2::Field
}

// A mapping from absolute cell position in the original table (column_type, column_index, row_index)
// to the position in Z
// We'll arrange Z in the order of 1 -> instance cells -> advice cells
fn generate_cell_mapping(
    instance: &[&[Option<Fp>]],
    advice: &[&[Option<Fp>]],
    fixed: &[&[Option<Fp>]],
    selectors: &[&[Option<bool>]],
    copy_constraints: &[CopyConstraint],
) -> HashMap<AbsoluteCellPosition, CCSValue> {
    let mut cell_mapping: HashMap<AbsoluteCellPosition, CCSValue> = HashMap::new();

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
            let value = cell.unwrap_or(Fp::ZERO);
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
            // TODO: Is it okay to initialize unassigned selector cell with false?
            let value = cell.unwrap_or(false).into();
            let cell_position = AbsoluteCellPosition {
                column_type: VirtualColumnType::Selector,
                column_index,
                row_index,
            };
            cell_mapping.insert(cell_position, CCSValue::InsideM(value));
        }
    }

    // Next, incorporate the copy constraints into the mapping.
    for (deduplicate_from, deduplicate_into) in generate_deduplication_map(copy_constraints) {
        let ccs_value = cell_mapping.get(&deduplicate_into).copied().unwrap();
        if let Some(pointer) = cell_mapping.get_mut(&deduplicate_from) {
            *pointer = ccs_value;
        }
    }

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

// A key-value map that represents the destination into which a cell gets deduplicated.
// Cells with greater ordering will get deduplicated into cells with less ordering.
fn generate_deduplication_map(
    copy_constraints: &[CopyConstraint],
) -> HashMap<AbsoluteCellPosition, AbsoluteCellPosition> {
    let mut deduplication_map = HashMap::new();

    for copy_constraint in copy_constraints.iter() {
        let left = AbsoluteCellPosition {
            column_type: copy_constraint.from_column_type.into(),
            column_index: copy_constraint.from_column_index,
            row_index: copy_constraint.from_row_index,
        };
        let right = AbsoluteCellPosition {
            column_type: copy_constraint.to_column_type.into(),
            column_index: copy_constraint.to_column_index,
            row_index: copy_constraint.to_row_index,
        };

        if let Some(pointer) = deduplication_map.get_mut(&left) {
            *pointer = right.min(*pointer)
        } else if left > right {
            deduplication_map.insert(left, right);
        }

        if let Some(pointer) = deduplication_map.get_mut(&right) {
            *pointer = left.min(*pointer)
        } else if left < right {
            deduplication_map.insert(right, left);
        }
    }

    deduplication_map
}

fn generate_mj<F: PrimeField>(
    query: Query,
    table_height: usize,
    witness_size: usize,
    cell_mapping: HashMap<AbsoluteCellPosition, CCSValue>,
) -> SparseMatrix<F> {
    let mut mj = SparseMatrix::empty();
    mj.n_cols = witness_size;
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

                // TODO: Do this somewhere else.
                let value = F::from_le_bytes_mod_order(&value.to_repr());

                // mj[y, 0] = value
                mj.coeffs.push(Vec::new());
                mj.coeffs.last_mut().unwrap().push((value, 0));
            }
        }
    }

    mj
}
