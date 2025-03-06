use ark_pallas::Fq;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::circuit::SimpleFloorPlanner;
use halo2_proofs::circuit::Value;
use halo2_proofs::dev::MockProver;
use halo2_proofs::pasta::Fp;
use halo2_proofs::plonk::Circuit;
use halo2_proofs::plonk::Column;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;
use halo2_proofs::plonk::Expression;
use halo2_proofs::plonk::Instance;
use halo2_proofs::plonk::TableColumn;
use halo2_proofs::poly::Rotation;
use halo2ccs::{convert_halo2_circuit, is_ccs_plus_satisfied};

//

#[test]
fn test_unassigned_lookup_table_success() -> Result<(), Error> {
    let k = 8;
    let circuit = Non0Circuit();
    let instance: [Fp; 250] = [1.into(); 250];
    let (ccs, z, lookups, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[&instance])?;

    let prover = MockProver::run(k, &circuit, vec![instance.to_vec()]).unwrap();
    assert!(prover.verify().is_ok());

    assert!(is_ccs_plus_satisfied(ccs, &z, lookups));

    Ok(())
}

#[test]
fn test_unassigned_lookup_table_fail() -> Result<(), Error> {
    let k = 8;
    let circuit = Non0Circuit();
    let instance: [Fp; 250] = [0.into(); 250];
    let (ccs, z, lookups, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[&instance])?;

    let prover = MockProver::run(k, &circuit, vec![instance.to_vec()]).unwrap();
    assert!(prover.verify().is_err());

    assert!(!is_ccs_plus_satisfied(ccs, &z, lookups));

    Ok(())
}

// all cells in the instance column must be non-0
#[derive(Debug, Clone)]
struct Non0Config {
    table: TableColumn,
    #[allow(dead_code)]
    instance: Column<Instance>,
}

#[derive(Debug)]
struct Non0Circuit();

impl Circuit<Fp> for Non0Circuit {
    type Config = Non0Config;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self()
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        let instance = meta.instance_column();
        let table = meta.lookup_table_column();

        // Without this reduce_n will remove these advice cells,
        // because there's no arithmetic constraints applied to these advice cells.
        // TODO: Is it appropriate that a cell that has to be in lookup table will get removed?
        // All lookup table in zcash/halo2 is fixed, so I feel like no sane person would write a circuit that has only lookup constraints with no arithmetic constraint
        meta.create_gate("meaningless constraint", |gate| {
            let instance = gate.query_instance(instance, Rotation::cur());
            vec![Expression::Scaled(Box::new(instance), 0.into())]
        });

        meta.lookup(|gate| {
            let instance = gate.query_instance(instance, Rotation::cur());
            vec![(instance, table)]
        });

        Self::Config { instance, table }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let fill_until = 200;

        // Fill all of the lookup table with some non-0 values.
        layouter.assign_table(
            || "non0 lookup table",
            |mut table| {
                for i in 0..fill_until {
                    table.assign_cell(
                        || "non0 cell",
                        config.table,
                        i,
                        || Value::known(Fp::from(i as u64) + Fp::ONE),
                    )?;
                }

                Ok(())
            },
        )?;

        Ok(())
    }
}
