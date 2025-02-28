#![allow(non_snake_case)]
use folding_schemes::arith::ccs::CCS;
use folding_schemes::utils::vec::is_zero_vec;
use halo2_proofs::circuit::Value;
use halo2_proofs::dump::dump_gates;
use halo2_proofs::dump::dump_lookups;
use halo2_proofs::dump::AssignmentDumper;
use halo2_proofs::plonk;
use halo2_proofs::plonk::*;
use lookup::check_lookup_satisfiability;
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
/// * `circuit` A Halo2 circuit you wish to convert
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
        Vec<(HashSet<usize>, Vec<ARKWORKS>)>,
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
    let advice: Vec<&[Option<HALO2>]> = cell_dumper.advice.iter().map(Vec::as_slice).collect();
    let fixed: Vec<&[Option<HALO2>]> = cell_dumper.fixed.iter().map(Vec::as_slice).collect();
    let selectors: Vec<&[bool]> = cell_dumper.selectors.iter().map(Vec::as_slice).collect();

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

    // Generate fixed lookup tables.
    // In the original CCS paper, there was only one lookup table T.
    // However, this implementation supports multiple lookup tables.
    let tables: Vec<Vec<ARKWORKS>> = lookups
        .iter()
        .map(|(_, table_expr)| {
            if let Expression::Fixed(query) = table_expr {
                fixed[query.column_index]
                    .iter()
                    .map(|cell| {
                        // Here we initialize unassigned cells in a lookup table with 0.
                        // This mimics Halo2's behavior.
                        // https://github.com/zcash/halo2/blob/fed6b000857f27e23ddb07454da8bde4697204f7/halo2_proofs/src/circuit/floor_planner/single_pass.rs#L180
                        ARKWORKS::from_le_bytes_mod_order(&cell.unwrap_or(0.into()).to_repr())
                    })
                    .collect()
            } else {
                // pse/halo2 lets table_expr to be something other than FixedQuery, but we're working on zcash/halo2.
                panic!("zcash/halo2 supports only fixed lookup tables.")
            }
        })
        .collect();

    // Generate multiple Ls.
    // In the original CCS paper, there was only one L.
    // But this implementation supports multiple lookup tables, so there should be one L for each T.
    let LandT = tables
        .into_iter()
        .enumerate()
        .map(|(lookup_index, T)| {
            // cell_mapping keeps track of z_index where evaluations of lookup inputs lies.
            // So we read it here.
            // Check generate_cell_mapping's implementation for more.
            let L = cell_mapping
                .iter()
                .filter_map(|(position, value)| {
                    if position.column_type == VirtualColumnType::LookupInput
                        && position.column_index == lookup_index
                    {
                        if let CCSValue::InsideZ(z_index) = value {
                            // This z_index is the o in the paper.
                            Some(z_index)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                })
                .copied()
                .collect();
            (L, T)
        })
        .collect();

    println!(
        "The number of advice/instance cells in the original Plonkish table: {}",
        (meta.num_advice_columns + meta.num_instance_columns) * (1 << k)
    );
    println!(
        "The height of the witness vector Z in the transpiled CCS circuit: {}",
        ccs_instance.n
    );

    Ok((ccs_instance, z, LandT))
}

/// Takes the output of `convert_halo2_circuit`, and check if the CCS+ instance is satisfied.
pub fn is_ccs_plus_satisfied<F: ark_ff::PrimeField>(
    ccs: CCS<F>,
    z: &[F],
    LandT: Vec<(HashSet<usize>, Vec<F>)>,
) -> bool {
    if let Ok(ccs_lhs) = ccs.eval_at_z(z) {
        if !is_zero_vec(&ccs_lhs) {
            return false;
        }
    } else {
        return false;
    };

    for (L, T) in LandT.iter() {
        let subset: Vec<F> = L.iter().map(|o| z[*o]).collect();
        if !check_lookup_satisfiability(&subset, T) {
            return false;
        }
    }

    return true;
}
