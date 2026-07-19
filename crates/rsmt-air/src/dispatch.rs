//! Heterogeneous-AIR enum dispatch for `p3-batch-stark` (DEVPLAN M4).
//!
//! `RsmtAir` wraps the seven table AIRs so they can share one batch commitment.
//! `LookupAir` is currently the empty default on every table (no buses yet): the
//! batch proves each table's **local** constraints through the real FRI stack.
//! Bus registrations are added table-by-table on top of this.

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
use crate::{TableAAir, TableBAir, TableCAir, TableDAir, TableFAir, TablePAir, TableRAir};

// Bus-free lookup impls (defaults) for tables whose buses aren't wired yet.
// Wired so far: Bus 7 (pow2) between Table P (send) and Table F (receive) — their
// real `LookupAir` impls live in their own modules.

/// Table B's `VectorizedPoseidon2Air` dominates the variant size; that is
/// inherent to the wrapper and the enum is only ever handled behind a reference.
#[allow(clippy::large_enum_variant)]
#[derive(Clone)]
pub enum RsmtAir {
    A(TableAAir),
    B(TableBAir),
    C(TableCAir),
    D(TableDAir),
    R(TableRAir),
    F(TableFAir),
    P(TablePAir),
}

macro_rules! dispatch {
    ($self:ident, $air:ident => $body:expr) => {
        match $self {
            Self::A($air) => $body,
            Self::B($air) => $body,
            Self::C($air) => $body,
            Self::D($air) => $body,
            Self::R($air) => $body,
            Self::F($air) => $body,
            Self::P($air) => $body,
        }
    };
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for RsmtAir {
    fn width(&self) -> usize {
        dispatch!(self, a => BaseAir::<F>::width(a))
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        dispatch!(self, a => BaseAir::<F>::preprocessed_trace(a))
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        dispatch!(self, a => BaseAir::<F>::main_next_row_columns(a))
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        dispatch!(self, a => BaseAir::<F>::preprocessed_next_row_columns(a))
    }
    fn num_public_values(&self) -> usize {
        dispatch!(self, a => BaseAir::<F>::num_public_values(a))
    }
}

impl<AB: AirBuilder<F = BabyBear>> Air<AB> for RsmtAir {
    fn eval(&self, builder: &mut AB) {
        dispatch!(self, a => Air::<AB>::eval(a, builder))
    }
}

impl<F: Field> LookupAir<F> for RsmtAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        dispatch!(self, a => LookupAir::<F>::add_lookup_columns(a))
    }
    fn get_lookups(&mut self) -> Vec<p3_lookup::Lookup<F>> {
        dispatch!(self, a => LookupAir::<F>::get_lookups(a))
    }
}

// ---------------------------------------------------------------------------
// R3 table set: A(reduced)/B/L/J/O/R/P
// ---------------------------------------------------------------------------

/// Heterogeneous-AIR enum for the R3 seven-table set `A/B/L/J/O/R/P`.
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
