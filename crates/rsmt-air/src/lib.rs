//! Table AIRs for the R3 RSMT statement (`DEVPLAN-R3.md`).
//!
//! Each table's column layout is a `#[repr(C)]` struct (one source of truth for
//! the width) and its AIR is validated with `p3_air::check_constraints` on
//! plan-generated traces; the seven tables share one batch commitment and their
//! LogUp buses balance end-to-end (see `rsmt-prover::r3round`).
//!
//! The R3 set is **A** (reduced proof rows, `table_ar`), **B** (Poseidon2), **L**
//! (fused canonical leaf), **J** (join coherence), **O** (canonical opening),
//! **R** (radix-1024 range), **P** (powers of two). The legacy `A/C/D/E/F`
//! tables were removed at the M11 cut-over.

mod cols;
pub mod dispatch;
pub mod table_ar;
pub mod table_b;
pub mod table_j;
pub mod table_l;
pub mod table_o;
pub mod table_p;
pub mod table_r;

pub use dispatch::R3Air;
pub use table_b::{P2_VECTOR_LEN, TableBAir};
pub use table_p::{TABLE_P_HEIGHT, TABLE_P_REAL, TABLE_P_WIDTH, TablePAir};
pub use table_r::{TABLE_R_HEIGHT, TABLE_R_WIDTH, TableRAir};
