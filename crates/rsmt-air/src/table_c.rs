//! Table C — leaf sponge (DEVPLAN M3). Three rows per leaf replay the additive
//! sponge (steps 0/1/2). Segmented **batch leaves then opened leaves** (D8
//! analogue) via a preprocessed `kind` bit.
//!
//! Local constraints (buses in M4): step-0 initialisation, the per-step
//! additive injection linking `state_in` of a step to `state_out` of the
//! previous step, key/value continuity within a leaf, `kind` booleanity, and
//! padding hygiene. The permutation `state_out = P2(state_in)` itself is tied
//! to Table B on Bus 2 (M4).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use rsmt_core::LIMBS;
use rsmt_hash::{DOMAIN_LEAF, STATE_WIDTH};
use rsmt_witness::{LeafKind, TracePlan};

use crate::cols::{cast, width_of};

/// Main columns (50): key[9], value[9], state_in[16], state_out[16].
#[repr(C)]
#[derive(Clone, Copy)]
pub struct CCols<T> {
    pub key: [T; LIMBS],
    pub value: [T; LIMBS],
    pub state_in: [T; STATE_WIDTH],
    pub state_out: [T; STATE_WIDTH],
}

/// Preprocessed columns (7).
#[repr(C)]
#[derive(Clone, Copy)]
pub struct CPrepCols<T> {
    pub leaf_idx: T,
    pub is_step_0: T,
    pub is_step_1: T,
    pub is_step_2: T,
    pub is_real: T,
    pub kind: T,           // 0 = batch, 1 = opened
    pub is_batch_step0: T, // step-0 of a batch leaf (Bus 6 receive gate)
}

pub const TABLE_C_WIDTH: usize = width_of::<CCols<u8>>();
pub const TABLE_C_PREP_WIDTH: usize = width_of::<CPrepCols<u8>>();

const _: () = assert!(TABLE_C_WIDTH == 50);

pub const BUS_LEAF_NAME: &str = "leaf";

#[derive(Clone)]
pub struct TableCAir {
    pub padded_height: usize,
    pub real_rows: usize,
    /// Number of batch-leaf rows (`3 · n_l`); rows below this are `kind = 0`.
    pub batch_rows: usize,
    pub num_lookups: usize,
}

impl TableCAir {
    pub const fn new(padded_height: usize, real_rows: usize, batch_rows: usize) -> Self {
        Self {
            padded_height,
            real_rows,
            batch_rows,
            num_lookups: 0,
        }
    }
}

impl<F: p3_field::Field> p3_lookup::LookupAir<F> for TableCAir {
    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let idx = self.num_lookups;
        self.num_lookups += 1;
        vec![idx]
    }

    #[allow(clippy::needless_range_loop)]
    fn get_lookups(&mut self) -> Vec<p3_lookup::Lookup<F>> {
        use p3_air::AirLayout;
        use p3_air::symbolic::{SymbolicAirBuilder, SymbolicExpression};
        use p3_lookup::{Direction, Kind};
        type SE<F> = SymbolicExpression<F>;
        self.num_lookups = 0;
        let sb = SymbolicAirBuilder::<F>::new(AirLayout {
            main_width: TABLE_C_WIDTH,
            preprocessed_width: TABLE_C_PREP_WIDTH,
            ..Default::default()
        });
        let main = sb.main();
        let ml = main.current_slice();
        let prep = sb.preprocessed();
        let pl = prep.current_slice();
        // Bus 4 (leaf): send (kind, idx, digest[8], key[9]) on step-2 rows.
        // C layout: key[0..9], value[9..18], state_in[18..34], state_out[34..50].
        // prep: leaf_idx(0), is_step_0(1), is_step_1(2), is_step_2(3), is_real(4), kind(5).
        let mut tuple: Vec<SE<F>> = vec![pl[5].into(), pl[0].into()];
        for j in 0..8 {
            tuple.push(ml[34 + j].into());
        }
        for j in 0..9 {
            tuple.push(ml[j].into());
        }
        let mut lookups = vec![p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(BUS_LEAF_NAME.to_string()),
            &[(tuple, pl[3].into(), Direction::Send)],
        )];

        // Bus 6 (batch): receive (idx, key[9], value[9]) on batch step-0 rows.
        let mut btuple: Vec<SE<F>> = vec![pl[0].into()];
        for j in 0..9 {
            btuple.push(ml[j].into()); // key
        }
        for j in 0..9 {
            btuple.push(ml[9 + j].into()); // value
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(BUS_BATCH_NAME.to_string()),
            &[(btuple, pl[6].into(), Direction::Receive)],
        ));

        // Bus 2 split (D17). Steps 0/1 feed forward → receive the full
        // (state_in[16], state_out[16]) on the feed-forward bus. Step 2 is
        // terminal → receive the digest (state_in[16], state_out[0..8]) on the
        // terminal bus. C prep: is_step_0=pl[1], is_step_1=pl[2], is_step_2=pl[3].
        // C layout: state_in[18..34], state_out[34..50].
        let ff_mult: SE<F> = SE::<F>::from(pl[1]) + SE::<F>::from(pl[2]);
        let mut ff: Vec<SE<F>> = Vec::with_capacity(32);
        for j in 0..16 {
            ff.push(ml[18 + j].into());
        }
        for j in 0..16 {
            ff.push(ml[34 + j].into());
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_b::BUS_P2FF_NAME.to_string()),
            &[(ff, ff_mult, Direction::Receive)],
        ));
        let mut term: Vec<SE<F>> = Vec::with_capacity(24);
        for j in 0..16 {
            term.push(ml[18 + j].into());
        }
        for j in 0..8 {
            term.push(ml[34 + j].into());
        }
        lookups.push(p3_lookup::LookupAir::register_lookup(
            self,
            Kind::Global(crate::table_b::BUS_P2TERM_NAME.to_string()),
            &[(term, pl[3].into(), Direction::Receive)],
        ));
        lookups
    }
}

pub const BUS_BATCH_NAME: &str = "batch";

impl<F: PrimeCharacteristicRing + Send + Sync> BaseAir<F> for TableCAir {
    fn width(&self) -> usize {
        TABLE_C_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let h = self.padded_height;
        let mut data = Vec::with_capacity(h * TABLE_C_PREP_WIDTH);
        for i in 0..h {
            let is_real = i < self.real_rows;
            // Per-kind leaf index (matches A's batch_idx / opened_idx on Bus 4).
            let leaf_idx = if !is_real {
                0
            } else if i < self.batch_rows {
                (i / 3) as u32
            } else {
                ((i - self.batch_rows) / 3) as u32
            };
            let step = if is_real { i % 3 } else { usize::MAX };
            let kind = is_real && i >= self.batch_rows;
            data.push(F::from_u32(leaf_idx));
            data.push(F::from_bool(is_real && step == 0));
            data.push(F::from_bool(is_real && step == 1));
            data.push(F::from_bool(is_real && step == 2));
            data.push(F::from_bool(is_real));
            data.push(F::from_bool(kind));
            data.push(F::from_bool(is_real && step == 0 && !kind));
        }
        Some(RowMajorMatrix::new(data, TABLE_C_PREP_WIDTH))
    }

    fn num_public_values(&self) -> usize {
        0
    }
}

impl<AB: AirBuilder> Air<AB> for TableCAir
where
    AB::F: Send,
{
    #[allow(clippy::type_complexity)]
    fn eval(&self, builder: &mut AB) {
        // Copy the row structs out as owned values so no builder borrow lingers
        // across the `assert_zero` calls below.
        let (local, next, pl, pn, row): (
            CCols<AB::Var>,
            CCols<AB::Var>,
            CPrepCols<AB::Var>,
            CPrepCols<AB::Var>,
            Vec<AB::Var>,
        ) = {
            let main = builder.main();
            let prep = builder.preprocessed();
            (
                *cast(main.current_slice()),
                *cast(main.next_slice()),
                *cast(prep.current_slice()),
                *cast(prep.next_slice()),
                main.current_slice().to_vec(),
            )
        };

        let one = AB::Expr::ONE;
        let e = |v: AB::Var| -> AB::Expr { v.into() };
        let domain_leaf = AB::Expr::from_u32(DOMAIN_LEAF);

        let is_real = e(pl.is_real);
        let is_step_0 = e(pl.is_step_0);
        let is_step_1_next = e(pn.is_step_1);
        let is_step_2_next = e(pn.is_step_2);

        // Padding hygiene: every witness column zero on non-real rows.
        let not_real = one.clone() - is_real.clone();
        for &cell in &row {
            builder.assert_zero(not_real.clone() * e(cell));
        }

        // kind booleanity (padding rows zero kind, so no is_real gate needed).
        builder.assert_zero(e(pl.kind) * (e(pl.kind) - one.clone()));

        // Step 0 init: state_in = [DOMAIN_LEAF, key[0..7], 0×8].
        builder.assert_zero(is_step_0.clone() * (e(local.state_in[0]) - domain_leaf));
        for j in 0..7 {
            builder.assert_zero(is_step_0.clone() * (e(local.state_in[1 + j]) - e(local.key[j])));
        }
        for j in 0..8 {
            builder.assert_zero(is_step_0.clone() * e(local.state_in[8 + j]));
        }

        // Step transitions: next.state_in = local.state_out + injection.
        for j in 0..STATE_WIDTH {
            let inj1: AB::Expr = match j {
                0 => e(local.key[7]),
                1 => e(local.key[8]),
                2..=7 => e(local.value[j - 2]),
                _ => AB::Expr::ZERO,
            };
            let inj2: AB::Expr = match j {
                0 => e(local.value[6]),
                1 => e(local.value[7]),
                2 => e(local.value[8]),
                _ => AB::Expr::ZERO,
            };
            builder.assert_zero(
                is_step_1_next.clone() * (e(next.state_in[j]) - e(local.state_out[j]) - inj1),
            );
            builder.assert_zero(
                is_step_2_next.clone() * (e(next.state_in[j]) - e(local.state_out[j]) - inj2),
            );
        }

        // key/value continuity within a leaf (same-leaf transitions only).
        let cont = is_step_1_next + is_step_2_next;
        for j in 0..LIMBS {
            builder.assert_zero(cont.clone() * (e(next.key[j]) - e(local.key[j])));
            builder.assert_zero(cont.clone() * (e(next.value[j]) - e(local.value[j])));
        }
    }
}

// -- trace generation -------------------------------------------------------

/// Build Table C's main trace from the plan (batch leaves, then opened leaves).
/// Returns `(trace, real_rows, height, batch_rows)`.
pub fn build_trace(plan: &TracePlan) -> (RowMajorMatrix<BabyBear>, usize, usize, usize) {
    let arena = plan.arena.entries();
    let leaves: Vec<_> = plan.c_batch.iter().chain(plan.c_opened.iter()).collect();
    let batch_rows = 3 * plan.c_batch.len();
    let real = 3 * leaves.len();
    let height = real.next_power_of_two().max(2);
    let mut data = Vec::with_capacity(height * TABLE_C_WIDTH);

    for leaf in &leaves {
        debug_assert!(leaf.kind == LeafKind::Batch || leaf.kind == LeafKind::Opened);
        for step in 0..3 {
            let io = arena[leaf.perm_idx[step] as usize];
            data.extend_from_slice(&leaf.key);
            data.extend_from_slice(&leaf.value);
            data.extend_from_slice(&io.input);
            data.extend_from_slice(&io.output);
        }
    }
    for _ in real..height {
        for _ in 0..TABLE_C_WIDTH {
            data.push(BabyBear::ZERO);
        }
    }
    (
        RowMajorMatrix::new(data, TABLE_C_WIDTH),
        real,
        height,
        batch_rows,
    )
}

#[cfg(test)]
mod tests;
