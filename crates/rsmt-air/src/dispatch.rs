//! Heterogeneous-AIR enum dispatch for `p3-batch-stark`.
//!
//! `R3Air` wraps the seven R3 table AIRs (`A/B/L/J/O/R/P`) so they share one
//! batch commitment. Each table's real `LookupAir` lives in its own module; the
//! buses balance end-to-end (see `rsmt-prover::r3round`).

use p3_air::{Air, AirBuilder, BaseAir};
use p3_baby_bear::BabyBear;
use p3_field::Field;
use p3_field::PrimeCharacteristicRing;
use p3_lookup::LookupAir;
use p3_matrix::dense::RowMajorMatrix;

use crate::table_ar::TableArAir;
use crate::table_j::TableJAir;
use crate::table_l::TableLAir;
use crate::table_o::TableOAir;
use crate::{TableBAir, TablePAir, TableRAir};

/// Heterogeneous-AIR enum for the R3 seven-table set `A/B/L/J/O/R/P`.
///
/// Table B's `VectorizedPoseidon2Air` dominates the variant size; that is
/// inherent to the wrapper and the enum is only ever handled behind a reference.
#[allow(clippy::large_enum_variant)]
#[derive(Clone)]
pub enum R3Air {
    A(TableArAir),
    B(TableBAir),
    L(TableLAir),
    J(TableJAir),
    O(TableOAir),
    R(TableRAir),
    P(TablePAir),
}

macro_rules! dispatch_r3 {
    ($self:ident, $air:ident => $body:expr) => {
        match $self {
            Self::A($air) => $body,
            Self::B($air) => $body,
            Self::L($air) => $body,
            Self::J($air) => $body,
            Self::O($air) => $body,
            Self::R($air) => $body,
            Self::P($air) => $body,
        }
    };
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for R3Air {
    fn width(&self) -> usize {
        dispatch_r3!(self, a => BaseAir::<F>::width(a))
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        dispatch_r3!(self, a => BaseAir::<F>::preprocessed_trace(a))
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        dispatch_r3!(self, a => BaseAir::<F>::main_next_row_columns(a))
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        dispatch_r3!(self, a => BaseAir::<F>::preprocessed_next_row_columns(a))
    }
    fn num_public_values(&self) -> usize {
        dispatch_r3!(self, a => BaseAir::<F>::num_public_values(a))
    }
}

impl<AB: AirBuilder<F = BabyBear>> Air<AB> for R3Air {
    fn eval(&self, builder: &mut AB) {
        dispatch_r3!(self, a => Air::<AB>::eval(a, builder))
    }
}

impl<F: Field> LookupAir<F> for R3Air {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        dispatch_r3!(self, a => LookupAir::<F>::add_lookup_columns(a))
    }
    fn get_lookups(&mut self) -> Vec<p3_lookup::Lookup<F>> {
        dispatch_r3!(self, a => LookupAir::<F>::get_lookups(a))
    }
}
