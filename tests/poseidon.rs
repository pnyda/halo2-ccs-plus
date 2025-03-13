use ark_pallas::Fq;
use ark_std::rand::rngs::OsRng;
use ff::Field;
use folding_schemes::utils::vec::is_zero_vec;
use halo2_gadgets::poseidon::primitives::P128Pow5T3 as OrchardNullifier;
use halo2_gadgets::poseidon::primitives::*;
use halo2_gadgets::poseidon::*;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::circuit::SimpleFloorPlanner;
use halo2_proofs::circuit::Value;
use halo2_proofs::dev::MockProver;
use halo2_proofs::pasta::Fp;
use halo2_proofs::plonk;
use halo2_proofs::plonk::Circuit;
use halo2_proofs::plonk::Column;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Instance;
use halo2ccs::convert_halo2_circuit;
use rayon::prelude::*;
use std::marker::PhantomData;

// Tests against a complex circuit that has multiple custom gates + copy constraints + no lookup

#[test]
fn test_poseidon_success() -> Result<(), halo2ccs::Error> {
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
    let circuit = HashCircuit::<OrchardNullifier, 3, 2, 2> {
        message: Value::known(message),
        _spec: PhantomData,
    };
    let (ccs, z, _, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[&[output]])?;

    let prover = MockProver::run(k, &circuit, vec![vec![output]]).unwrap();
    assert_eq!(prover.verify(), Ok(()));
    assert!(is_zero_vec(&ccs.eval_at_z(&z).unwrap()));

    Ok(())
}

#[test]
fn test_poseidon_fail() -> Result<(), halo2ccs::Error> {
    let message = [Fp::random(OsRng), Fp::random(OsRng)];
    let output = 0.into();

    let k = 6;
    let circuit = HashCircuit::<OrchardNullifier, 3, 2, 2> {
        message: Value::known(message),
        _spec: PhantomData,
    };
    let (ccs, z, _, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[&[output]])?;

    let prover = MockProver::run(k, &circuit, vec![vec![output]]).unwrap();
    assert!(prover.verify().is_err());
    assert!(!is_zero_vec(&ccs.eval_at_z(&z).unwrap()));

    Ok(())
}

#[test]
fn test_poseidon_no_unconstrained_z() -> Result<(), halo2ccs::Error> {
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
    let circuit = HashCircuit::<OrchardNullifier, 3, 2, 2> {
        message: Value::known(message),
        _spec: PhantomData,
    };
    let (ccs, z, _, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[&[output]])?;

    let no_unconstrained_z = (1..z.len()).into_par_iter().all(|i| {
        let mut z = z.clone();
        z[i] = 123456789.into();
        !is_zero_vec(&ccs.eval_at_z(&z).unwrap())
    });
    assert!(no_unconstrained_z);

    Ok(())
}

#[test]
fn test_poseidon_no_meaningless_constraint() -> Result<(), halo2ccs::Error> {
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
    let circuit = HashCircuit::<OrchardNullifier, 3, 2, 2> {
        message: Value::known(message),
        _spec: PhantomData,
    };
    let (ccs, _z, _, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[&[output]])?;

    let does_meaningless_constraint_exist = (0..ccs.m).into_par_iter().any(|row_index| {
        ccs.M.iter().all(|matrix| {
            matrix.coeffs[row_index]
                .iter()
                .all(|(value, _position)| *value == 0.into())
        })
    });
    assert!(!does_meaningless_constraint_exist);

    Ok(())
}

#[test]
fn test_poseidon_no_empty_matrix() -> Result<(), halo2ccs::Error> {
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
    let circuit = HashCircuit::<OrchardNullifier, 3, 2, 2> {
        message: Value::known(message),
        _spec: PhantomData,
    };
    let (ccs, _z, _, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[&[output]])?;

    let num_empty_matrices = ccs
        .M
        .into_par_iter()
        .filter(|matrix| {
            matrix
                .coeffs
                .iter()
                .all(|row| row.iter().all(|(value, _position)| *value == 0.into()))
        })
        .count();
    assert!(
        0 >= num_empty_matrices,
        "num_empty_matrices: {}",
        num_empty_matrices
    );

    Ok(())
}

#[test]
#[allow(non_snake_case)]
fn test_poseidon_no_duplicate_S() -> Result<(), halo2ccs::Error> {
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
    let circuit = HashCircuit::<OrchardNullifier, 3, 2, 2> {
        message: Value::known(message),
        _spec: PhantomData,
    };
    let (mut ccs, _z, _, _) = convert_halo2_circuit::<_, _, Fq>(k, &circuit, &[&[output]])?;

    for multiset in ccs.S.iter_mut() {
        multiset.sort();
    }
    ccs.S.sort();

    let is_there_duplicate_S = ccs
        .S
        .iter()
        .skip(1)
        .zip(ccs.S.iter())
        .any(|(next, prev)| prev == next);
    assert!(!is_there_duplicate_S);

    Ok(())
}

#[derive(Clone)]
struct HashConfig<const WIDTH: usize, const RATE: usize> {
    pow5: Pow5Config<Fp, WIDTH, RATE>,
    instance_column: Column<Instance>,
}

// Taken from https://github.com/zcash/halo2/blob/halo2_proofs-0.3.0/halo2_gadgets/src/poseidon/pow5.rs#L719
struct HashCircuit<S: Spec<Fp, WIDTH, RATE>, const WIDTH: usize, const RATE: usize, const L: usize>
{
    message: Value<[Fp; L]>,
    _spec: PhantomData<S>,
}

impl<S: Spec<Fp, WIDTH, RATE>, const WIDTH: usize, const RATE: usize, const L: usize> Circuit<Fp>
    for HashCircuit<S, WIDTH, RATE, L>
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
    ) -> Result<(), plonk::Error> {
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

                let message: Result<Vec<_>, plonk::Error> = (0..L).map(message_word).collect();
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
