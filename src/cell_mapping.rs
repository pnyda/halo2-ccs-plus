use crate::query::AbsoluteCellPosition;
use crate::Query;
use crate::VirtualColumnType;
use halo2_proofs::dump::CopyConstraint;
use halo2_proofs::plonk::Expression;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CCSValue<F: ark_ff::PrimeField> {
    InsideZ(usize), // z_index
    InsideM(F),     // fixed value
}

// A mapping from absolute cell position in the original table (column_type, column_index, row_index)
// to the position in Z
pub(crate) fn generate_cell_mapping<
    HALO2: ff::PrimeField<Repr = [u8; 32]>,
    ARKWORKS: ark_ff::PrimeField,
>(
    // These have to have the shape [[cell assignment; number of rows]; number of columns]
    // None means unassigned cell
    instance: &[&[Option<HALO2>]],
    advice: &[&[Option<HALO2>]],
    fixed: &[&[Option<HALO2>]],
    selectors: &[&[bool]],
    copy_constraints: &[CopyConstraint],
    lookup_inputs: &[Expression<HALO2>],
) -> HashMap<AbsoluteCellPosition, CCSValue<ARKWORKS>> {
    let mut cell_mapping: HashMap<AbsoluteCellPosition, CCSValue<ARKWORKS>> = HashMap::new();
    let mut z_height = 1;

    for (column_index, column) in instance.into_iter().enumerate() {
        for (row_index, _) in column.into_iter().enumerate() {
            let cell_position = AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index,
                row_index,
            };
            cell_mapping.insert(cell_position, CCSValue::InsideZ(z_height));
            z_height += 1;
        }
    }

    for (column_index, column) in advice.into_iter().enumerate() {
        for (row_index, _) in column.into_iter().enumerate() {
            let cell_position = AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index,
                row_index,
            };
            cell_mapping.insert(cell_position, CCSValue::InsideZ(z_height));
            z_height += 1;
        }
    }

    for (column_index, column) in fixed.into_iter().enumerate() {
        for (row_index, cell) in column.into_iter().enumerate() {
            // Here we initialize unassigned fixed cell with 0.
            // This mimics Halo2's behavior.
            // https://github.com/zcash/halo2/blob/fed6b000857f27e23ddb07454da8bde4697204f7/halo2_proofs/src/poly/domain.rs#L189
            let value = ARKWORKS::from_le_bytes_mod_order(&cell.unwrap_or(0.into()).to_repr());
            let cell_position = AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index,
                row_index,
            };
            cell_mapping.insert(cell_position, CCSValue::InsideM(value));
        }
    }

    for (column_index, column) in selectors.into_iter().enumerate() {
        for (row_index, cell) in column.into_iter().enumerate() {
            let value = (*cell).into();
            let cell_position = AbsoluteCellPosition {
                column_type: VirtualColumnType::Selector,
                column_index,
                row_index,
            };
            cell_mapping.insert(cell_position, CCSValue::InsideM(value));
        }
    }

    // Next, incorporate the copy constraints into the mapping.
    deduplicate_witness(&mut cell_mapping, copy_constraints);

    // Next, incorporate lookup constraints into the mapping.
    let table_height = advice
        .first()
        .map(|column| column.len())
        .or_else(|| instance.first().map(|column| column.len()))
        .or_else(|| fixed.first().map(|column| column.len()))
        .or_else(|| selectors.first().map(|column| column.len()))
        .expect("The width of the Plonkish table is 0. Can't continue.");

    for (lookup_index, lookup_input) in lookup_inputs.iter().enumerate() {
        for y in 0..table_height {
            let key = AbsoluteCellPosition {
                column_type: VirtualColumnType::LookupInput,
                column_index: lookup_index,
                row_index: y,
            };
            let value = match lookup_input {
                // If the lookup input is just a query, we don't add new witness to Z.
                // Instead we store in cell_mapping a reference to an existing entry in Z.
                Expression::Advice(query) => cell_mapping
                    .get(&Query::Advice(*query).cell_position(y, table_height))
                    .copied()
                    .unwrap(),
                Expression::Instance(query) => cell_mapping
                    .get(&Query::Instance(*query).cell_position(y, table_height))
                    .copied()
                    .unwrap(),
                // If the lookup input is a complex Expression, we will create new witness
                _ => {
                    z_height += 1;
                    CCSValue::InsideZ(z_height - 1)
                }
            };
            cell_mapping.insert(key, value);
        }
    }

    cell_mapping
}

// Cells with greater ordering will get deduplicated into cells with less ordering.
fn deduplicate_witness<F: ark_ff::PrimeField>(
    cell_mapping: &mut HashMap<AbsoluteCellPosition, CCSValue<F>>,
    copy_constraints: &[CopyConstraint],
) {
    // Each element in HashSet<AbsoluteCellPosition> must have the same assignment.
    let mut equalities: Vec<HashSet<AbsoluteCellPosition>> = Vec::new();

    for copy_constraint in copy_constraints.into_iter() {
        // These 2 cells must have the same assignment.
        let cell1 = AbsoluteCellPosition {
            column_type: copy_constraint.from_column_type.into(),
            column_index: copy_constraint.from_column_index,
            row_index: copy_constraint.from_row_index,
        };
        let cell2 = AbsoluteCellPosition {
            column_type: copy_constraint.to_column_type.into(),
            column_index: copy_constraint.to_column_index,
            row_index: copy_constraint.to_row_index,
        };

        // The use of .iter().position() here must slow down the code, but I prioritize the readability of the code.
        let cell1_belongs_in = equalities
            .iter()
            .position(|must_be_same| must_be_same.contains(&cell1));
        let cell2_belongs_in = equalities
            .iter()
            .position(|must_be_same| must_be_same.contains(&cell2));

        match (cell1_belongs_in, cell2_belongs_in) {
            (None, None) => {
                // When neither of the cells are in `equalities`, we add a new entry.
                equalities.push(HashSet::new());
                equalities.last_mut().unwrap().insert(cell1);
                equalities.last_mut().unwrap().insert(cell2);
            }
            (Some(cell1_belongs_in), None) => {
                // When we encounter a new copy constraint A = B when we already have B = C,
                // `equalities` must be updated to be [A = B = C], not [A = B, B = C]
                equalities[cell1_belongs_in].insert(cell2);
            }
            (None, Some(cell2_belongs_in)) => {
                equalities[cell2_belongs_in].insert(cell1);
            }
            (Some(cell1_belongs_in), Some(cell2_belongs_in)) => {
                // Let's say we have `equalities` [A = C, B = C].
                // And then we encountered a new copy constraint A = B.
                // Then the new `equalities` must be [A = B = C], not [A = C, B = C, A = B].
                let to_be_merged = equalities.remove(cell2_belongs_in);
                equalities[cell1_belongs_in].extend(to_be_merged);
            }
        }
    }

    for must_be_same in equalities.into_iter() {
        let mut sorted: Vec<AbsoluteCellPosition> = must_be_same.into_iter().collect();
        sorted.sort();

        // For each equality set, we deduplicate into the cell position with the least ordering.
        let deduplicate_into = sorted.first().unwrap();
        // It's okay to unwrap here because an element of `equalities` will never have length fewer than 2.

        for deduplicate_from in sorted.iter().skip(1) {
            *cell_mapping.get_mut(&deduplicate_from).unwrap() =
                cell_mapping.get(&deduplicate_into).copied().unwrap();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CCSValue;
    use ark_pallas::Fq;
    use halo2_proofs::pasta::Fp;
    use halo2_proofs::plonk::AdviceQuery;
    use halo2_proofs::plonk::Any;
    use halo2_proofs::plonk::InstanceQuery;
    use halo2_proofs::poly::Rotation;

    #[cfg(test)]
    #[test]
    fn test_duplicate_witness() {
        let mut actual: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = HashMap::new();
        actual.insert(
            // cell A
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(1),
        );
        actual.insert(
            // cell B
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideZ(2),
        );
        actual.insert(
            // cell C
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideZ(3),
        );
        actual.insert(
            // cell D
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 3,
            },
            CCSValue::InsideZ(4),
        );

        let copy_constraints = vec![
            CopyConstraint {
                // B = C
                from_column_type: Any::Advice,
                from_column_index: 0,
                from_row_index: 2,
                to_column_type: Any::Advice,
                to_column_index: 0,
                to_row_index: 1,
            },
            CopyConstraint {
                // C = D
                from_column_type: Any::Advice,
                from_column_index: 0,
                from_row_index: 3,
                to_column_type: Any::Advice,
                to_column_index: 0,
                to_row_index: 2,
            },
            CopyConstraint {
                // B = A
                from_column_type: Any::Advice,
                from_column_index: 0,
                from_row_index: 0,
                to_column_type: Any::Advice,
                to_column_index: 0,
                to_row_index: 1,
            },
        ];

        deduplicate_witness(&mut actual, &copy_constraints);

        // All get deduplicated into A
        let mut expect = HashMap::new();
        expect.insert(
            // cell A
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(1),
        );
        expect.insert(
            // cell B
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideZ(1),
        );
        expect.insert(
            // cell C
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideZ(1),
        );
        expect.insert(
            // cell D
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 3,
            },
            CCSValue::InsideZ(1),
        );

        assert_eq!(actual, expect);
    }

    #[cfg(test)]
    #[test]
    fn test_duplicate_witness_instance() {
        let mut actual: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = HashMap::new();
        actual.insert(
            // cell A
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(2),
        );
        actual.insert(
            // cell B
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideZ(3),
        );
        actual.insert(
            // cell C
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideZ(4),
        );
        actual.insert(
            // cell D
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(1),
        );

        let copy_constraints = vec![
            CopyConstraint {
                // B = C
                from_column_type: Any::Advice,
                from_column_index: 0,
                from_row_index: 2,
                to_column_type: Any::Advice,
                to_column_index: 0,
                to_row_index: 1,
            },
            CopyConstraint {
                // C = D
                from_column_type: Any::Instance,
                from_column_index: 0,
                from_row_index: 0,
                to_column_type: Any::Advice,
                to_column_index: 0,
                to_row_index: 2,
            },
            CopyConstraint {
                // B = A
                from_column_type: Any::Advice,
                from_column_index: 0,
                from_row_index: 0,
                to_column_type: Any::Advice,
                to_column_index: 0,
                to_row_index: 1,
            },
        ];

        deduplicate_witness(&mut actual, &copy_constraints);

        // All get deduplicated into D
        let mut expect = HashMap::new();
        expect.insert(
            // cell A
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(1),
        );
        expect.insert(
            // cell B
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideZ(1),
        );
        expect.insert(
            // cell C
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideZ(1),
        );
        expect.insert(
            // cell D
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(1),
        );

        assert_eq!(actual, expect);
    }

    #[cfg(test)]
    #[test]
    fn test_duplicate_witness_fixed() {
        let mut actual: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = HashMap::new();
        actual.insert(
            // cell A
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(1),
        );
        actual.insert(
            // cell B
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideM(123456789.into()),
        );
        actual.insert(
            // cell C
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideZ(2),
        );
        actual.insert(
            // cell D
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideZ(3),
        );

        let copy_constraints = vec![
            CopyConstraint {
                // A = B
                from_column_type: Any::Advice,
                from_column_index: 0,
                from_row_index: 0,
                to_column_type: Any::Fixed,
                to_column_index: 0,
                to_row_index: 0,
            },
            CopyConstraint {
                // C = D
                from_column_type: Any::Advice,
                from_column_index: 0,
                from_row_index: 1,
                to_column_type: Any::Advice,
                to_column_index: 0,
                to_row_index: 2,
            },
            CopyConstraint {
                // D = A
                from_column_type: Any::Advice,
                from_column_index: 0,
                from_row_index: 0,
                to_column_type: Any::Advice,
                to_column_index: 0,
                to_row_index: 2,
            },
        ];

        deduplicate_witness(&mut actual, &copy_constraints);

        // All get deduplicated into B
        let mut expect = HashMap::new();
        expect.insert(
            // cell A
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideM(123456789.into()),
        );
        expect.insert(
            // cell B
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideM(123456789.into()),
        );
        expect.insert(
            // cell C
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideM(123456789.into()),
        );
        expect.insert(
            // cell D
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideM(123456789.into()),
        );

        assert_eq!(actual, expect);
    }

    #[cfg(test)]
    #[test]
    fn test_generate_cell_mapping() {
        // Meaningless assignments
        let instance = [[Some(Fp::from(5)), None, None, None]];
        let advice = [[
            Some(Fp::from(1)),
            Some(Fp::from(2)),
            Some(Fp::from(3)),
            Some(Fp::from(5)),
        ]];
        let fixed = [[Some(Fp::from(1)), Some(Fp::from(2)), None, None]];
        let selectors = [[true, true, true, false]];
        // Meaningless copy constraints
        let copy_constraints = [
            CopyConstraint {
                from_column_type: Any::Fixed,
                from_column_index: 0,
                from_row_index: 0,
                to_column_type: Any::Advice,
                to_column_index: 0,
                to_row_index: 0,
            },
            CopyConstraint {
                from_column_type: Any::Fixed,
                from_column_index: 0,
                from_row_index: 1,
                to_column_type: Any::Advice,
                to_column_index: 0,
                to_row_index: 1,
            },
        ];
        // Meaningless lookups
        let lookup_inputs: [Expression<Fp>; 2] = [
            // We need to test 2 lookup inputs here because generate_cell_mapping behaves differently depending on if the lookup input is a simple query or a complex expression
            Expression::Advice(AdviceQuery {
                index: 0,
                column_index: 0,
                rotation: Rotation(0),
            }),
            Expression::Scaled(
                Box::new(Expression::Instance(InstanceQuery {
                    index: 0,
                    column_index: 0,
                    rotation: Rotation(0),
                })),
                2.into(),
            ),
        ];

        let mut expect: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = HashMap::new();
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideZ(1),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideZ(2),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideZ(3),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index: 0,
                row_index: 3,
            },
            CCSValue::InsideZ(4),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideM(1.into()),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideM(2.into()),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideZ(7),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: 0,
                row_index: 3,
            },
            CCSValue::InsideZ(8),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideM(1.into()),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideM(2.into()),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideM(0.into()),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: 0,
                row_index: 3,
            },
            CCSValue::InsideM(0.into()),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Selector,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideM(1.into()),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Selector,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideM(1.into()),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Selector,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideM(1.into()),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::Selector,
                column_index: 0,
                row_index: 3,
            },
            CCSValue::InsideM(0.into()),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::LookupInput,
                column_index: 0,
                row_index: 0,
            },
            CCSValue::InsideM(1.into()),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::LookupInput,
                column_index: 0,
                row_index: 1,
            },
            CCSValue::InsideM(2.into()),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::LookupInput,
                column_index: 0,
                row_index: 2,
            },
            CCSValue::InsideZ(7),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::LookupInput,
                column_index: 0,
                row_index: 3,
            },
            CCSValue::InsideZ(8),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::LookupInput,
                column_index: 1,
                row_index: 0,
            },
            CCSValue::InsideZ(9),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::LookupInput,
                column_index: 1,
                row_index: 1,
            },
            CCSValue::InsideZ(10),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::LookupInput,
                column_index: 1,
                row_index: 2,
            },
            CCSValue::InsideZ(11),
        );
        expect.insert(
            AbsoluteCellPosition {
                column_type: VirtualColumnType::LookupInput,
                column_index: 1,
                row_index: 3,
            },
            CCSValue::InsideZ(12),
        );

        let actual: HashMap<AbsoluteCellPosition, CCSValue<Fq>> = generate_cell_mapping(
            &instance.each_ref().map(|x| &x[..]), // It feels weird that we have to do this manually
            &advice.each_ref().map(|x| &x[..]),
            &fixed.each_ref().map(|x| &x[..]),
            &selectors.each_ref().map(|x| &x[..]),
            &copy_constraints,
            &lookup_inputs,
        );
        assert_eq!(actual, expect);
    }
}
