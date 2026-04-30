//! Heterogeneous AIR enum-dispatch wrapper for `p3-batch-stark::prove_batch`.

use p3_air::{Air, AirBuilder, BaseAir};
use p3_baby_bear::BabyBear;
use p3_field::Field;
use p3_field::PrimeCharacteristicRing;
use p3_lookup::{Lookup, LookupAir};
use p3_matrix::dense::RowMajorMatrix;

use crate::{TableAAir, TableBAir, TableCAir, TableDAir, TableEAir, TableFAir};

#[derive(Clone)]
pub enum RsmtAir {
    A(TableAAir),
    B(TableBAir),
    F(TableFAir),
    E(TableEAir),
    C(TableCAir),
    D(TableDAir),
}

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for RsmtAir {
    fn width(&self) -> usize {
        match self {
            Self::A(a) => <TableAAir as BaseAir<F>>::width(a),
            Self::B(a) => <TableBAir as BaseAir<F>>::width(a),
            Self::F(a) => <TableFAir as BaseAir<F>>::width(a),
            Self::E(a) => <TableEAir as BaseAir<F>>::width(a),
            Self::C(a) => <TableCAir as BaseAir<F>>::width(a),
            Self::D(a) => <TableDAir as BaseAir<F>>::width(a),
        }
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            Self::A(a) => <TableAAir as BaseAir<F>>::preprocessed_trace(a),
            Self::B(a) => <TableBAir as BaseAir<F>>::preprocessed_trace(a),
            Self::F(a) => <TableFAir as BaseAir<F>>::preprocessed_trace(a),
            Self::E(a) => <TableEAir as BaseAir<F>>::preprocessed_trace(a),
            Self::C(a) => <TableCAir as BaseAir<F>>::preprocessed_trace(a),
            Self::D(a) => <TableDAir as BaseAir<F>>::preprocessed_trace(a),
        }
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        match self {
            Self::A(a) => <TableAAir as BaseAir<F>>::main_next_row_columns(a),
            Self::B(a) => <TableBAir as BaseAir<F>>::main_next_row_columns(a),
            Self::F(a) => <TableFAir as BaseAir<F>>::main_next_row_columns(a),
            Self::E(a) => <TableEAir as BaseAir<F>>::main_next_row_columns(a),
            Self::C(a) => <TableCAir as BaseAir<F>>::main_next_row_columns(a),
            Self::D(a) => <TableDAir as BaseAir<F>>::main_next_row_columns(a),
        }
    }

    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        match self {
            Self::A(a) => <TableAAir as BaseAir<F>>::preprocessed_next_row_columns(a),
            Self::B(a) => <TableBAir as BaseAir<F>>::preprocessed_next_row_columns(a),
            Self::F(a) => <TableFAir as BaseAir<F>>::preprocessed_next_row_columns(a),
            Self::E(a) => <TableEAir as BaseAir<F>>::preprocessed_next_row_columns(a),
            Self::C(a) => <TableCAir as BaseAir<F>>::preprocessed_next_row_columns(a),
            Self::D(a) => <TableDAir as BaseAir<F>>::preprocessed_next_row_columns(a),
        }
    }

    fn num_public_values(&self) -> usize {
        match self {
            Self::A(a) => <TableAAir as BaseAir<F>>::num_public_values(a),
            Self::B(a) => <TableBAir as BaseAir<F>>::num_public_values(a),
            Self::F(a) => <TableFAir as BaseAir<F>>::num_public_values(a),
            Self::E(a) => <TableEAir as BaseAir<F>>::num_public_values(a),
            Self::C(a) => <TableCAir as BaseAir<F>>::num_public_values(a),
            Self::D(a) => <TableDAir as BaseAir<F>>::num_public_values(a),
        }
    }
}

impl<AB: AirBuilder<F = BabyBear>> Air<AB> for RsmtAir {
    fn eval(&self, builder: &mut AB) {
        match self {
            Self::A(a) => <TableAAir as Air<AB>>::eval(a, builder),
            Self::B(a) => <TableBAir as Air<AB>>::eval(a, builder),
            Self::F(a) => <TableFAir as Air<AB>>::eval(a, builder),
            Self::E(a) => <TableEAir as Air<AB>>::eval(a, builder),
            Self::C(a) => <TableCAir as Air<AB>>::eval(a, builder),
            Self::D(a) => <TableDAir as Air<AB>>::eval(a, builder),
        }
    }
}

impl<F: Field> LookupAir<F> for RsmtAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        match self {
            Self::A(a) => <TableAAir as LookupAir<F>>::add_lookup_columns(a),
            Self::B(a) => <TableBAir as LookupAir<F>>::add_lookup_columns(a),
            Self::F(a) => <TableFAir as LookupAir<F>>::add_lookup_columns(a),
            Self::E(a) => <TableEAir as LookupAir<F>>::add_lookup_columns(a),
            Self::C(a) => <TableCAir as LookupAir<F>>::add_lookup_columns(a),
            Self::D(a) => <TableDAir as LookupAir<F>>::add_lookup_columns(a),
        }
    }
    fn get_lookups(&mut self) -> Vec<Lookup<F>> {
        match self {
            Self::A(a) => <TableAAir as LookupAir<F>>::get_lookups(a),
            Self::B(a) => <TableBAir as LookupAir<F>>::get_lookups(a),
            Self::F(a) => <TableFAir as LookupAir<F>>::get_lookups(a),
            Self::E(a) => <TableEAir as LookupAir<F>>::get_lookups(a),
            Self::C(a) => <TableCAir as LookupAir<F>>::get_lookups(a),
            Self::D(a) => <TableDAir as LookupAir<F>>::get_lookups(a),
        }
    }
}
