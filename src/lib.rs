// Taken from https://github.com/icemelon/halo2-examples/blob/master/src/fibonacci/example2.rs

use folding_schemes::arith::ccs::CCS;
use folding_schemes::utils::vec::SparseMatrix;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::dump::{dump_gates, dump_lookups, AssignmentDumper, CopyConstraint};
use halo2_proofs::pasta::Fp;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};
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
    k: u32,
    monomials: &[Monomial<Fp>],
    num_instance_columns: usize,
    copy_constraints: &[CopyConstraint],
    fixed: Vec<Vec<Option<Fp>>>,
    selectors: Vec<Vec<Option<bool>>>,
) -> HashMap<AbsoluteCellPosition, CCSValue> {
    // First, generate the mapping with no respect to copy constraints.
    let table_height = 1 << k;
    let mut cell_mapping: HashMap<AbsoluteCellPosition, CCSValue> = HashMap::new();

    for monomial in monomials.iter() {
        for query in monomial.variables.iter() {
            for y in 0usize..table_height {
                match query {
                    Query::Instance(query) => {
                        let row_index =
                            (y as i32 + query.rotation.0).rem_euclid(table_height as i32) as usize;
                        let z_index = 1 + query.column_index * table_height + row_index;
                        let cell_position = AbsoluteCellPosition {
                            column_type: VirtualColumnType::Instance,
                            column_index: query.column_index,
                            row_index,
                        };
                        cell_mapping.insert(cell_position, CCSValue::InsideZ(z_index));
                    }
                    Query::Advice(query) => {
                        let row_index =
                            (y as i32 + query.rotation.0).rem_euclid(table_height as i32) as usize;
                        let z_index = 1
                            + (num_instance_columns + query.column_index) * table_height
                            + row_index;
                        let cell_position = AbsoluteCellPosition {
                            column_type: VirtualColumnType::Advice,
                            column_index: query.column_index,
                            row_index,
                        };
                        cell_mapping.insert(cell_position, CCSValue::InsideZ(z_index));
                    }
                    Query::Fixed(query) => {
                        let row_index =
                            (y as i32 + query.rotation.0).rem_euclid(table_height as i32) as usize;
                        // TODO: Is it okay to initialize an unassigned cell with 0?
                        let value = fixed[query.column_index][row_index].unwrap_or(Fp::ZERO);
                        let cell_position = AbsoluteCellPosition {
                            column_type: VirtualColumnType::Fixed,
                            column_index: query.column_index,
                            row_index,
                        };
                        cell_mapping.insert(cell_position, CCSValue::InsideM(value));
                    }
                    Query::Selector(query) => {
                        let row_index = y;
                        // TODO: Is it okay to initialize an unassigned selector cell with false?
                        let value = selectors[query.0][row_index].unwrap_or(false);
                        let cell_position = AbsoluteCellPosition {
                            column_type: VirtualColumnType::Selector,
                            column_index: query.0,
                            row_index,
                        };
                        cell_mapping.insert(cell_position, CCSValue::InsideM(value.into()));
                    }
                }
            }
        }
    }

    cell_mapping
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum VirtualColumnType {
    Instance,
    Advice,
    Fixed,
    Selector,
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
