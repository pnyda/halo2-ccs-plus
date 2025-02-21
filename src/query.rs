// Reference to a cell, relative to the current row
use halo2_proofs::plonk::Any;
use halo2_proofs::plonk::FixedQuery;
use halo2_proofs::plonk::{AdviceQuery, InstanceQuery, Selector};
use std::cmp::Ordering;
use std::hash::Hash;

// I use this Ord impl for witness deduplication.
// Cells with greater ordering will get deduplicated into cells with less ordering.
// If there was a copy constraint between an advice cell and an instance cell,
//   the former will get deduplicated into the latter.
// If there was a copy constraint between an advice cell and a fixed cell,
//   the former will get deduplicated into the latter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum VirtualColumnType {
    LookupInput,
    Selector,
    Fixed,
    Instance,
    Advice,
}

impl From<Any> for VirtualColumnType {
    fn from(value: Any) -> Self {
        match value {
            Any::Instance => VirtualColumnType::Instance,
            Any::Advice => VirtualColumnType::Advice,
            Any::Fixed => VirtualColumnType::Fixed,
        }
    }
}

// Cell position in a Plonkish table.
// Unlike Query, which represents a cell position *relative* to the current row, this struct represents an absolute position in the Plonkish table.

// column_index will be assigned for each column_type, starting from 0.
// For example if we had 1 instance column and 1 advice column, column_index of both will be 0.
// if we had 0 instance column and 2 advice column, first column_index is 0, second column_index is 1.

// This feels unintuitive but Halo2's internal works that way so I didn't bother to change it.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct AbsoluteCellPosition {
    pub(crate) column_type: VirtualColumnType,
    pub(crate) column_index: usize,
    pub(crate) row_index: usize,
}

// I use this Ord impl for witness deduplication.
// Cells with greater ordering will get deduplicated into cells with less ordering.
impl Ord for AbsoluteCellPosition {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.column_type.cmp(&other.column_type) {
            Ordering::Equal => match self.column_index.cmp(&other.column_index) {
                Ordering::Equal => self.row_index.cmp(&other.row_index),
                ordering => ordering,
            },
            ordering => ordering,
        }
    }
}

impl PartialOrd for AbsoluteCellPosition {
    fn partial_cmp(&self, other: &AbsoluteCellPosition) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum Query {
    Fixed(FixedQuery),
    Advice(AdviceQuery),
    Instance(InstanceQuery),
    Selector(Selector),
    LookupInput(usize), // the index of lookup constraint
}

impl Query {
    // As I said Query is a reference to a cell *relative* to the current row.
    // This method converts that relative reference to an absolute cell position, given the current row.
    pub(crate) fn cell_position(self, at_row: usize, table_height: usize) -> AbsoluteCellPosition {
        match self {
            Query::Selector(query) => AbsoluteCellPosition {
                column_type: VirtualColumnType::Selector,
                column_index: query.0,
                row_index: at_row,
            },
            Query::Fixed(query) => AbsoluteCellPosition {
                column_type: VirtualColumnType::Fixed,
                column_index: query.column_index,
                row_index: (at_row as i32 + query.rotation.0).rem_euclid(table_height as i32)
                    as usize,
            },
            Query::Instance(query) => AbsoluteCellPosition {
                column_type: VirtualColumnType::Instance,
                column_index: query.column_index,
                row_index: (at_row as i32 + query.rotation.0).rem_euclid(table_height as i32)
                    as usize,
            },
            Query::Advice(query) => AbsoluteCellPosition {
                column_type: VirtualColumnType::Advice,
                column_index: query.column_index,
                row_index: (at_row as i32 + query.rotation.0).rem_euclid(table_height as i32)
                    as usize,
            },
            Query::LookupInput(index) => AbsoluteCellPosition {
                column_type: VirtualColumnType::LookupInput,
                column_index: index,
                row_index: at_row,
            },
        }
    }
}

impl PartialEq for Query {
    fn eq(&self, other: &Self) -> bool {
        // This implementation only cares about the information CCS+ cares about.
        // I want QueryA == QueryB to hold every time when QueryA and QueryB is essentially the same query, ignoring Halo2's menial internal data.
        // For example query.index is just data Halo2 internally uses to keep track of queries.
        // So this impl ignores query.index

        match (self, other) {
            (Self::Fixed(lhs), Self::Fixed(rhs)) => {
                lhs.rotation == rhs.rotation && lhs.column_index == rhs.column_index
            }
            (Self::Advice(lhs), Self::Advice(rhs)) => {
                lhs.rotation == rhs.rotation && lhs.column_index == rhs.column_index
            }
            (Self::Instance(lhs), Self::Instance(rhs)) => {
                lhs.rotation == rhs.rotation && lhs.column_index == rhs.column_index
            }
            (Self::Selector(lhs), Self::Selector(rhs)) => lhs.0 == rhs.0,
            (Self::LookupInput(lhs), Self::LookupInput(rhs)) => lhs == rhs,
            _ => false,
        }
    }
}
