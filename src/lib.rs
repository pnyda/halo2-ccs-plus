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
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Display;

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

#[derive(Debug)]
pub enum Error {
    Halo2(plonk::Error),
    NoWitness,
    TableWidth0,
    TableHeight0,
    UnassignedLookupTable,
}

impl From<plonk::Error> for Error {
    fn from(src: plonk::Error) -> Self {
        Error::Halo2(src)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Halo2(err) => err.fmt(f),
            Self::NoWitness => {
                f.write_str("We're about to generate a CCS instance with n<2. Can't continue.")
            }
            Self::TableWidth0 => {
                f.write_str("The width of the Plonkish table is 0. Can't continue.")
            }
            Self::TableHeight0 => {
                f.write_str("The height of the Plonkish table is 0. Can't continue.")
            }
            Self::UnassignedLookupTable => {
                f.write_str("A fixed column used in lookup argument had an unassigned cell. This happens when the user forgot to call assign_table on the fixed column.")
            }
        }
    }
}

/// Converts a Halo2 circuit into a sonobe CCS instance.
///
/// - `k` log_2(the height of the Plonkish table)
/// - `circuit` A Halo2 circuit you wish to convert
/// - `instance` Assignments to the instance columns. The length of this slice must equal the number of the instance columns in `circuit`.
///
/// Returns
/// - A CCS instance
/// - The witness vector Z
/// - Lookup constraints
/// - A map from a cell position in the original Plonkish table to the position in `Z`.
///
/// lookup constraints takes a form of Vec<(L, T)> where for every o ∈ L, z\[o\] must be in T.
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
        HashMap<AbsoluteCellPosition, usize>,
    ),
    Error,
> {
    let mut meta = ConstraintSystem::<HALO2>::default();
    // This line updates meta.num_instance_columns
    let config = C::configure(&mut meta);
    // This line reads meta.num_instance_columns
    let mut cell_dumper: AssignmentDumper<HALO2> = AssignmentDumper::new(k, &meta);

    // instance_option has the same shape as cell_dumper.instance
    let mut instance_option: Vec<Vec<Option<HALO2>>> = cell_dumper
        .instance
        .iter()
        .map(|column| vec![None; column.len()])
        .collect();

    for (column_index, column) in instance.iter().enumerate() {
        for (row_index, cell) in column.iter().enumerate() {
            // Assign an instance cell
            cell_dumper.instance[column_index][row_index] = Value::known(*cell);
            // Value does not implement unwrap so I need to keep track of the assignments in Option...
            instance_option[column_index][row_index] = Some(*cell);
        }
    }

    C::FloorPlanner::synthesize(&mut cell_dumper, circuit, config, meta.constants.clone())?;

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
    )?;

    let custom_gates = dump_gates::<HALO2, C>()?;

    let ccs_instance: CCS<ARKWORKS> =
        generate_ccs_instance(&custom_gates, &mut cell_mapping, &lookup_inputs)?;
    let z: Vec<ARKWORKS> = generate_z(
        &selectors,
        &fixed,
        &instance_option,
        &advice,
        &cell_mapping,
        &lookup_inputs,
    )?;

    // Generate fixed lookup tables.
    // In the original CCS paper, there was only one lookup table T.
    // However, this implementation supports multiple lookup tables.
    let mut tables: Vec<HashSet<ARKWORKS>> = Vec::new();
    for (_, table_expr) in lookups {
        tables.push(HashSet::new());

        if let Expression::Fixed(query) = table_expr {
            // zcash/halo2 only allows table_expr to be Expression::Fixed

            // In Halo2, you use assign_table to assign a value in a lookup table.
            // When you call assign_table only on some rows, and leave rest of the column unassigned, assign_table will automatically fill the rest of the column with duplicates of already assigned values.
            // This means that, we won't encounter unassigned None cell here, except the case where the user didn't call assign_table, not even once.

            for cell in fixed[query.column_index] {
                if let Some(cell) = cell {
                    tables
                        .last_mut()
                        .unwrap()
                        .insert(ARKWORKS::from_le_bytes_mod_order(&cell.to_repr()));
                } else {
                    return Err(Error::UnassignedLookupTable);
                }
            }
        } else {
            // pse/halo2 lets table_expr to be something other than FixedQuery, but we're working on zcash/halo2.
            panic!("zcash/halo2 supports only fixed lookup tables.")
        }
    }

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

    let z_index_map: HashMap<AbsoluteCellPosition, usize> = cell_mapping
        .into_iter()
        .filter_map(|(key, value)| {
            if let CCSValue::InsideZ(z_index) = value {
                // Expose the mapping between advice/instance cell position and z_index,
                // Users might want to add constraints to those witnesses later in Sonobe.
                Some((key, z_index))
            } else {
                // There's no point in exposing fixed cell assignments.
                None
            }
        })
        .collect();

    Ok((ccs_instance, z, LandT, z_index_map))
}

/// Takes the output of `convert_halo2_circuit`, and check if the CCS+ instance is satisfied.
pub fn is_ccs_plus_satisfied<F: ark_ff::PrimeField>(
    ccs: CCS<F>,
    z: &[F],
    LandT: Vec<(HashSet<usize>, HashSet<F>)>,
) -> bool {
    if let Ok(ccs_lhs) = ccs.eval_at_z(z) {
        if !is_zero_vec(&ccs_lhs) {
            return false;
        }
    } else {
        return false;
    };

    for (L, T) in LandT.iter() {
        let subset: HashSet<F> = L.iter().map(|o| z[*o]).collect();
        if !check_lookup_satisfiability(&subset, T) {
            return false;
        }
    }

    return true;
}
