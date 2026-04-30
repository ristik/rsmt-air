//! Table C (leaf sponge) witness builder. Three rows per `L` op.

use p3_baby_bear::BabyBear;
use p3_baby_bear::default_babybear_poseidon2_16;
use p3_field::PrimeCharacteristicRing;
use p3_symmetric::Permutation;
use rayon::prelude::*;

use rsmt_hash::{DIGEST_WIDTH, DOMAIN_LEAF, LIMBS, STATE_WIDTH, pack_biguint, pack_value_32};

#[derive(Clone, Debug)]
pub struct TableCRow {
    pub leaf_idx: u32,
    pub absorb_step: u8,
    pub key: [BabyBear; LIMBS],
    pub value: [BabyBear; LIMBS],
    pub cap_in: [BabyBear; DIGEST_WIDTH],
    pub state_in: [BabyBear; STATE_WIDTH],
    pub state_out: [BabyBear; STATE_WIDTH],
}

/// Build Table C rows from the (already sorted) batch.
///
/// Each leaf produces three rows whose internal sponge state chains within
/// the leaf only — there is no cross-leaf dependency, so leaves are processed
/// in parallel. Output ordering matches the sequential implementation
/// (`leaf_idx` 0,0,0,1,1,1,…).
pub fn build_table_c(sorted_batch: &[(num_bigint::BigUint, Vec<u8>)]) -> Vec<TableCRow> {
    sorted_batch
        .par_iter()
        .enumerate()
        .flat_map_iter(|(i, (k, v))| {
            let perm = default_babybear_poseidon2_16();
            let key = pack_biguint(k);
            let value = pack_value_32(v);
            let mut prev_out = [BabyBear::ZERO; STATE_WIDTH];
            let mut out: [Option<TableCRow>; 3] = [None, None, None];

            for step in 0..3u8 {
                let mut state_in = prev_out;
                match step {
                    0 => {
                        state_in[0] += BabyBear::from_u32(DOMAIN_LEAF);
                        for j in 0..7 {
                            state_in[1 + j] += key[j];
                        }
                    }
                    1 => {
                        state_in[0] += key[7];
                        state_in[1] += key[8];
                        for j in 0..6 {
                            state_in[2 + j] += value[j];
                        }
                    }
                    2 => {
                        state_in[0] += value[6];
                        state_in[1] += value[7];
                        state_in[2] += value[8];
                    }
                    _ => unreachable!(),
                }
                let mut state_out = state_in;
                perm.permute_mut(&mut state_out);

                let mut cap_in = [BabyBear::ZERO; DIGEST_WIDTH];
                cap_in.copy_from_slice(&prev_out[8..16]);

                out[step as usize] = Some(TableCRow {
                    leaf_idx: i as u32,
                    absorb_step: step,
                    key,
                    value,
                    cap_in,
                    state_in,
                    state_out,
                });

                prev_out = state_out;
            }
            out.into_iter().map(Option::unwrap)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use rand::{RngExt, SeedableRng};
    use rand_xoshiro::Xoshiro256PlusPlus;

    use rsmt_core::Hasher;
    use rsmt_hash::Poseidon2Hasher;

    use super::*;

    #[test]
    fn table_c_last_step_matches_leaf_hash() {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(2024);
        let batch: Vec<(BigUint, Vec<u8>)> = (0..8)
            .map(|_| {
                let mut k = [0u8; 32];
                rng.fill(&mut k);
                let mut v = [0u8; 32];
                rng.fill(&mut v);
                (BigUint::from_bytes_be(&k), v.to_vec())
            })
            .collect();
        let rows = build_table_c(&batch);
        assert_eq!(rows.len(), batch.len() * 3);
        for (i, (k, v)) in batch.iter().enumerate() {
            let expected = Poseidon2Hasher::hash_leaf(k, v);
            let last = &rows[3 * i + 2];
            for j in 0..DIGEST_WIDTH {
                assert_eq!(last.state_out[j], expected[j]);
            }
        }
    }
}
