use ark_pallas::Fq;
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
use halo2_proofs::plonk::TableColumn;
use halo2_proofs::poly::Rotation;
use halo2ccs::convert_halo2_circuit;
use std::collections::HashSet;

// Tests for cases where the lookup input is a simple query
// The code behaves differently depending on if the lookup input is complex or not so I need to test both cases

#[test]
fn test_range_success() -> Result<(), Error> {
    let k = 9;
    let circuit = RangeCircuit {
        bytes: vec![1.into(), 2.into(), 3.into(), 255.into()],
    };
    let (_ccs, z, lookups) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[])?;

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    let is_lookup_satisfied = lookups.into_iter().all(|(z_indices, table)| {
        z_indices
            .into_iter()
            .map(|z_index| z[z_index])
            .collect::<HashSet<_>>()
            .is_subset(&table)
    });
    assert!(is_lookup_satisfied);

    Ok(())
}

#[test]
fn test_range_failure() -> Result<(), Error> {
    let k = 9;
    let circuit = RangeCircuit {
        bytes: vec![1.into(), 2.into(), 3.into(), 256.into()],
    };
    let (_ccs, z, lookups) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[])?;

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert!(prover.verify().is_err());

    let is_lookup_satisfied = lookups.into_iter().all(|(z_indices, table)| {
        z_indices
            .into_iter()
            .map(|z_index| z[z_index])
            .collect::<HashSet<_>>()
            .is_subset(&table)
    });
    assert!(!is_lookup_satisfied);

    Ok(())
}

#[derive(Debug, Clone)]
struct RangeConfig {
    table: TableColumn,
    advice: Column<Advice>,
}

#[derive(Debug)]
struct RangeCircuit {
    bytes: Vec<Fp>,
}

impl Circuit<Fp> for RangeCircuit {
    type Config = RangeConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { bytes: Vec::new() }
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        let advice = meta.advice_column();
        let table = meta.lookup_table_column();

        // Without this reduce_n will remove these advice cells,
        // because there's no arithmetic constraints applied to these advice cells.
        // TODO: Is it appropriate that a cell that has to be in lookup table will get removed?
        // All lookup table in zcash/halo2 is fixed, so I feel like no sane person would write a circuit that has only lookup constraints with no arithmetic constraint
        meta.create_gate("meaningless constraint", |gate| {
            let advice = gate.query_advice(advice, Rotation::cur());
            vec![Expression::Scaled(Box::new(advice.clone()), 0.into())]
        });

        meta.lookup(|gate| {
            let advice = gate.query_advice(advice, Rotation::cur());
            vec![(advice, table)]
        });

        Self::Config { advice, table }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "aa",
            |mut region| {
                for (i, byte) in self.bytes.iter().enumerate() {
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
