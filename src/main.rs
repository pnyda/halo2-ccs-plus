// Taken from https://github.com/icemelon/halo2-examples/blob/master/src/fibonacci/example2.rs

use halo2_proofs::arithmetic::Field;
use halo2_proofs::dump::{dump_gates, dump_lookups, AssignmentDumper};
use halo2_proofs::pasta::Fp;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};
use std::marker::PhantomData;

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

fn main() -> Result<(), Error> {
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

    Ok(())
}
