use ark_pallas::Fq;
use ff::Field;
use folding_schemes::utils::vec::is_zero_vec;
use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::circuit::SimpleFloorPlanner;
use halo2_proofs::dev::MockProver;
use halo2_proofs::pasta::Fp;
use halo2_proofs::plonk::Advice;
use halo2_proofs::plonk::Circuit;
use halo2_proofs::plonk::Column;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;
use halo2_proofs::plonk::Instance;
use halo2_proofs::plonk::Selector;
use halo2_proofs::poly::Rotation;
use halo2ccs::convert_halo2_circuit;
use std::marker::PhantomData;

// Tests against a simple circuit that has only one custom gate + copy constraints + no lookup

#[test]
fn test_fibonacci_success() -> Result<(), Error> {
    let instance_column: Vec<Fp> = vec![1.into(), 1.into(), 55.into()];

    let k = 4;
    let circuit = FibonacciCircuit(PhantomData);
    let (ccs, z, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[&instance_column])?;

    let prover = MockProver::run(k, &circuit, vec![instance_column]).unwrap();
    assert!(prover.verify().is_ok());
    assert!(is_zero_vec(&ccs.eval_at_z(&z).unwrap()));

    Ok(())
}

#[test]
fn test_fibonacci_fail_when_changing_z() -> Result<(), Error> {
    let instance_column: Vec<Fp> = vec![1.into(), 1.into(), 55.into()];

    let k = 4;
    let circuit = FibonacciCircuit(PhantomData);
    let (ccs, mut z, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[&instance_column])?;

    let prover = MockProver::run(k, &circuit, vec![instance_column]).unwrap();
    assert!(prover.verify().is_ok());

    dbg!(z.len());

    // You can NOT change elements of z which have been set to 0 - unassigned cells in halo2
    z[10] = 10.into();
    assert!(!is_zero_vec(&ccs.eval_at_z(&z).unwrap()));

    Ok(())
}

#[test]
fn test_fibonacci_fail() -> Result<(), Error> {
    let instance_column: Vec<Fp> = vec![1.into(), 1.into(), 54.into()];

    let k = 4;
    let circuit = FibonacciCircuit(PhantomData);
    let (ccs, z, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[&instance_column])?;

    let prover = MockProver::run(k, &circuit, vec![instance_column]).unwrap();
    assert!(prover.verify().is_err());
    assert!(!is_zero_vec(&ccs.eval_at_z(&z).unwrap()));

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
    fn construct(config: FibonacciConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
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

    fn assign(
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

    fn expose_public(
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
