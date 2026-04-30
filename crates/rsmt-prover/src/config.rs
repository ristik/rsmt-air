//! Tunable FRI/PCS parameters exposed to callers.
//!
//! Trade-off: `log_blowup` and `num_queries` together determine the
//! conjectured soundness budget `log_blowup * num_queries +
//! query_proof_of_work_bits` (see `p3_fri::FriParameters`). Increasing
//! `log_blowup` makes each query worth more bits (so `num_queries` can
//! drop, shrinking the proof) at the cost of a larger LDE on the prover.
//! `query_proof_of_work_bits` shifts a fixed amount of work onto the
//! prover (a one-time grind) in exchange for fewer queries.

use p3_fri::FriParameters;

#[derive(Clone, Debug)]
pub struct ProverConfig {
    pub log_blowup: usize,
    pub log_final_poly_len: usize,
    pub max_log_arity: usize,
    pub num_queries: usize,
    pub commit_proof_of_work_bits: usize,
    pub query_proof_of_work_bits: usize,
}

impl Default for ProverConfig {
    /// Matches `FriParameters::new_benchmark_high_arity`.
    fn default() -> Self {
        Self {
            log_blowup: 1,
            log_final_poly_len: 0,
            max_log_arity: 3,
            num_queries: 100,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 16,
        }
    }
}

impl ProverConfig {
    pub fn to_fri_params<M>(&self, mmcs: M) -> FriParameters<M> {
        FriParameters {
            log_blowup: self.log_blowup,
            log_final_poly_len: self.log_final_poly_len,
            max_log_arity: self.max_log_arity,
            num_queries: self.num_queries,
            commit_proof_of_work_bits: self.commit_proof_of_work_bits,
            query_proof_of_work_bits: self.query_proof_of_work_bits,
            mmcs,
        }
    }

    /// Conjectured soundness bits (ethSTARK).
    pub fn conjectured_soundness_bits(&self) -> usize {
        self.log_blowup * self.num_queries + self.query_proof_of_work_bits
    }
}
