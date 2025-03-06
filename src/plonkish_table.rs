use halo2_proofs::plonk;
use halo2_proofs::plonk::AdviceQuery;
use halo2_proofs::plonk::Expression;
use halo2_proofs::plonk::FixedQuery;
use halo2_proofs::plonk::InstanceQuery;
use halo2_proofs::plonk::Selector;

use crate::AbsoluteCellPosition;
use crate::VirtualColumnType;

pub(crate) struct PlonkishTable<ARKWORKS: ark_ff::PrimeField> {
    // Note that table_height might not equal the height of Vec
    pub(crate) k: usize,
    // selector[x][y] is ith selector column's value at row y
    pub(crate) selector: Vec<Vec<ARKWORKS>>,
    // fixed[x][y] is xth fixed column's value at row y
    pub(crate) fixed: Vec<Vec<ARKWORKS>>,
    // advice[x][y] is xth advice column's value at row y
    pub(crate) advice: Vec<Vec<ARKWORKS>>,
    // instance[x][y] is xth instance column's value at row y
    pub(crate) instance: Vec<Vec<ARKWORKS>>,
    // Note that the height of a column Vec might not equal table_height, due to blinding factors.
    // column_vec.len() == table_height - num_blinding_factors - 1
    // What is blinding factors? See https://zcash.github.io/halo2/design/proving-system/lookup.html#zero-knowledge-adjustment
    pub(crate) lookup_inputs: Vec<Vec<ARKWORKS>>,
}

impl<ARKWORKS: ark_ff::PrimeField> PlonkishTable<ARKWORKS> {
    pub(crate) fn new(k: usize) -> Self {
        Self {
            k,
            selector: Vec::new(),
            fixed: Vec::new(),
            advice: Vec::new(),
            instance: Vec::new(),
            lookup_inputs: Vec::new(),
        }
    }

    pub(crate) fn fill_from_halo2<HALO2: ff::PrimeField<Repr = [u8; 32]>>(
        &mut self,
        selector: &[Vec<bool>],
        fixed: &[Vec<Option<HALO2>>],
        advice: &[Vec<Option<HALO2>>],
        instance: &[Vec<Option<HALO2>>],
    ) {
        self.selector = selector
            .iter()
            .map(|column| {
                column
                    .iter()
                    .map(|cell| if *cell { 1.into() } else { 0.into() })
                    .collect()
            })
            .collect();
        self.fixed = fixed
            .iter()
            .map(|column| {
                column
                    .iter()
                    .map(|opt| {
                        // Here we initialize an unassigned fixed cell with 0.
                        // This mimics Halo2's behavior.
                        // https://github.com/zcash/halo2/issues/614
                        ARKWORKS::from_le_bytes_mod_order(&opt.unwrap_or(0.into()).to_repr())
                    })
                    .collect()
            })
            .collect();
        self.advice = advice
            .iter()
            .map(|column| {
                column
                    .iter()
                    .map(|opt| {
                        // Here we initialize an unassigned advice cell with 0.
                        // This mimics Halo2's behavior.
                        // https://github.com/zcash/halo2/issues/614
                        ARKWORKS::from_le_bytes_mod_order(&opt.unwrap_or(0.into()).to_repr())
                    })
                    .collect()
            })
            .collect();
        self.instance = instance
            .iter()
            .map(|column| {
                column
                    .iter()
                    .map(|opt| {
                        // Here we initialize an unassigned instance cell with 0.
                        // This mimics Halo2's behavior.
                        // https://github.com/zcash/halo2/issues/614
                        ARKWORKS::from_le_bytes_mod_order(&opt.unwrap_or(0.into()).to_repr())
                    })
                    .collect()
            })
            .collect();
    }

    pub(crate) fn evaluate_lookup_inputs<HALO2: ff::PrimeField<Repr = [u8; 32]>>(
        &mut self,
        lookup_inputs: &[Expression<HALO2>],
    ) -> Result<(), crate::Error> {
        self.lookup_inputs.clear();

        for lookup_input in lookup_inputs {
            self.lookup_inputs.push(Vec::new());

            for y in 0..self.usable_rows()? {
                // halo2::Expression::evaluate lets us evaluate a Expression.
                // but lets us specify what to do when it encountered each enum variants
                let evaluation: ARKWORKS = lookup_input.evaluate(
                    // Exrpession::Constant
                    &|constant| Ok(ARKWORKS::from_le_bytes_mod_order(&constant.to_repr())),
                    // Expression::Selector
                    &|query: Selector| {
                        self.selector
                            .get(query.0)
                            .and_then(|column| column.get(y).copied())
                            .ok_or(plonk::Error::BoundsFailure)
                    },
                    // Expression::Fixed
                    &|query: FixedQuery| {
                        self.fixed
                            .get(query.column_index)
                            .and_then(|column| {
                                let row_index = (y as i32 + query.rotation.0)
                                    .rem_euclid(self.table_height() as i32)
                                    as usize;
                                column.get(row_index).copied()
                            })
                            .ok_or(plonk::Error::BoundsFailure)
                    },
                    // Expression::Advice
                    &|query: AdviceQuery| {
                        self.advice
                            .get(query.column_index)
                            .and_then(|column| {
                                let row_index = (y as i32 + query.rotation.0)
                                    .rem_euclid(self.table_height() as i32)
                                    as usize;
                                column.get(row_index).copied()
                            })
                            .ok_or(plonk::Error::BoundsFailure)
                    },
                    // Expression::
                    &|query: InstanceQuery| {
                        self.instance
                            .get(query.column_index)
                            .and_then(|column| {
                                let row_index = (y as i32 + query.rotation.0)
                                    .rem_euclid(self.table_height() as i32)
                                    as usize;
                                column.get(row_index).copied()
                            })
                            .ok_or(plonk::Error::BoundsFailure)
                    },
                    &|x| x.map(|x| -x),
                    &|lhs, rhs| lhs.and_then(|lhs| rhs.map(|rhs| lhs + rhs)),
                    &|lhs, rhs| lhs.and_then(|lhs| rhs.map(|rhs| lhs * rhs)),
                    &|lhs, constant| {
                        lhs.map(|lhs| lhs * ARKWORKS::from_le_bytes_mod_order(&constant.to_repr()))
                    },
                )?;

                self.lookup_inputs.last_mut().unwrap().push(evaluation);
            }
        }

        Ok(())
    }

    // returns table_height - num_blinding_factors - 1
    // AssignmentDumper gives us Vec of length of table_height - num_blinding_factors - 1
    pub(crate) fn usable_rows(&self) -> Result<usize, crate::Error> {
        self.selector
            .first()
            .map(|column| column.len())
            .or_else(|| self.fixed.first().map(|column| column.len()))
            .or_else(|| self.advice.first().map(|column| column.len()))
            .or_else(|| self.instance.first().map(|column| column.len()))
            .ok_or(crate::Error::TableWidth0)
    }

    pub(crate) fn table_height(&self) -> usize {
        1 << self.k
    }

    pub(crate) fn get(&self, cell: AbsoluteCellPosition) -> Option<ARKWORKS> {
        match cell.column_type {
            VirtualColumnType::Selector => self
                .selector
                .get(cell.column_index)
                .and_then(|column| column.get(cell.row_index))
                .copied(),
            VirtualColumnType::Advice => self
                .advice
                .get(cell.column_index)
                .and_then(|column| column.get(cell.row_index))
                .copied(),
            VirtualColumnType::Instance => self
                .instance
                .get(cell.column_index)
                .and_then(|column| column.get(cell.row_index))
                .copied(),
            VirtualColumnType::Fixed => self
                .fixed
                .get(cell.column_index)
                .and_then(|column| column.get(cell.row_index))
                .copied(),
            VirtualColumnType::LookupInput => self
                .lookup_inputs
                .get(cell.column_index)
                .and_then(|column| column.get(cell.row_index))
                .copied(),
        }
    }
}
