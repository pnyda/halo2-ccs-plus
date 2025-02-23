#![allow(non_snake_case)]
use folding_schemes::arith::ccs::CCS;
use halo2_proofs::circuit::Value;
use halo2_proofs::dump::dump_gates;
use halo2_proofs::dump::dump_lookups;
use halo2_proofs::dump::AssignmentDumper;
use halo2_proofs::plonk;
use halo2_proofs::plonk::*;
use std::collections::HashSet;

mod query;
use query::*;
mod cell_mapping;
mod monomial;
use cell_mapping::*;
mod ccs;
mod lookup;
use ccs::*;

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
    let instance_option: Vec<&[Option<HALO2>]> =
        instance_option.iter().map(Vec::as_slice).collect();
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

    dbg!(cell_dumper.copy_constraints.len());

    let lookups = dump_lookups::<HALO2, C>()?;
    let lookup_inputs: Vec<Expression<HALO2>> =
        lookups.iter().map(|(input, _)| input).cloned().collect();
    let mut cell_mapping = generate_cell_mapping(
        &instance_option,
        &advice,
        &fixed,
        &selectors,
        &cell_dumper.copy_constraints,
        &lookup_inputs,
    );

    let custom_gates = dump_gates::<HALO2, C>()?;
    let ccs_instance: CCS<ARKWORKS> =
        generate_ccs_instance(&custom_gates, &mut cell_mapping, &lookup_inputs);
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

                    // Here we initialize unassigned cells in a lookup table with 0.
                    // This mimics Halo2's behavior.
                    // https://github.com/zcash/halo2/blob/fed6b000857f27e23ddb07454da8bde4697204f7/halo2_proofs/src/circuit/floor_planner/single_pass.rs#L180

                    ARKWORKS::from_le_bytes_mod_order(&scalar.to_repr())
                })
                .collect()
        })
        .collect();

    let LandT = (0..lookups.len())
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

    println!(
        "The number of advice cells in the original Plonkish table: {}",
        advice.len() * advice[0].len()
    );
    println!(
        "The number of witnesses in the transpiled CCS circuit: {}",
        z.len() - ccs_instance.l
    );

    Ok((ccs_instance, z, LandT))
}
