use ark_pallas::Fq;
use ff::Field;
use folding_schemes::utils::vec::is_zero_vec;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::circuit::SimpleFloorPlanner;
use halo2_proofs::circuit::Value;
use halo2_proofs::dev::MockProver;
use halo2_proofs::pasta::Fp;
use halo2_proofs::plonk::Advice;
use halo2_proofs::plonk::Circuit;
use halo2_proofs::plonk::Column;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;
use halo2_proofs::plonk::Expression;
use halo2_proofs::plonk::Fixed;
use halo2_proofs::plonk::TableColumn;
use halo2_proofs::poly::Rotation;
use halo2ccs::{convert_halo2_circuit, is_ccs_plus_satisfied};
use rayon::prelude::*;

// tests for the cases where the lookup input is a complex Expression
// The code behaves differently depending on if the lookup input is complex or not so I need to test both cases

#[test]
fn test_less_than_success() -> Result<(), Error> {
    let k = 9;
    let circuit = LessThanCircuit {
        less_than_200: vec![1.into(), 2.into(), 3.into(), 199.into()],
    };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    let (ccs, z, lookups, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[])?;
    assert!(is_ccs_plus_satisfied(ccs, &z, lookups));

    Ok(())
}

#[test]
fn test_less_than_failure() -> Result<(), Error> {
    let k = 9;
    let circuit = LessThanCircuit {
        less_than_200: vec![1.into(), 2.into(), 3.into(), 200.into()],
    };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert!(prover.verify().is_err());

    let (ccs, z, lookups, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[])?;
    assert!(!is_ccs_plus_satisfied(ccs, &z, lookups));

    Ok(())
}

#[test]
fn test_less_than_no_unconstrained_z() -> Result<(), Error> {
    let k = 9;
    let circuit = LessThanCircuit {
        less_than_200: vec![1.into(), 2.into(), 3.into(), 199.into()],
    };

    let (ccs, z, _, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[])?;
    assert!(is_zero_vec(&ccs.eval_at_z(&z).unwrap()));

    let no_unconstrained_z = (1..z.len()).into_par_iter().all(|i| {
        let mut z = z.clone();
        z[i] = 123456789.into();
        !is_zero_vec(&ccs.eval_at_z(&z).unwrap())
    });
    assert!(no_unconstrained_z);

    Ok(())
}

#[derive(Debug)]
struct LessThanCircuit {
    less_than_200: Vec<Fp>,
}

#[derive(Debug, Clone)]
struct LessThanConfig {
    table: TableColumn,
    advice: Column<Advice>,
    is_enabled: Column<Fixed>,
}

impl Circuit<Fp> for LessThanCircuit {
    type Config = LessThanConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            less_than_200: Vec::new(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        let advice = meta.advice_column();
        let table = meta.lookup_table_column();
        let is_enabled = meta.fixed_column();

        meta.lookup(|gate| {
            let advice = gate.query_advice(advice, Rotation::cur());
            let is_enabled = gate.query_fixed(is_enabled);
            vec![(
                is_enabled * (advice + Expression::Constant(Fp::from(56))),
                table,
            )]
        });

        Self::Config {
            advice,
            table,
            is_enabled,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "aa",
            |mut region| {
                for (i, byte) in self.less_than_200.iter().enumerate() {
                    region.assign_fixed(|| "cc", config.is_enabled, i, || Value::known(Fp::ONE))?;
                    region.assign_advice(|| "bb", config.advice, i, || Value::known(*byte))?;
                }
                Ok(())
            },
        )?;

        layouter.assign_table(
            || "range check",
            |mut table| {
                for i in 0..(1 << 8) {
                    table.assign_cell(
                        || "a byte",
                        config.table,
                        i,
                        || Value::known(Fp::from(i as u64)),
                    )?;
                }
                Ok(())
            },
        )?;

        Ok(())
    }
}
