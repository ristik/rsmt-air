//! AIR definitions for the six RSMT3 tables (A, F, B, C, D, E) and the
//! six LogUp buses linking them.
//!
//! Currently only Table A is implemented (local constraints; LogUp not yet
//! wired). It can be validated with `p3_air::check_constraints` to gain
//! confidence in the constraint logic ahead of bus integration.

pub mod dispatch;
pub mod table_a;
pub mod table_b;
pub mod table_c;
pub mod table_d;
pub mod table_e;
pub mod table_f;

pub use dispatch::RsmtAir;

pub use table_a::{TABLE_A_PREP_WIDTH, TABLE_A_WIDTH, TableAAir};
pub use table_b::{P2_VECTOR_LEN, TableBAir};
pub use table_c::{TABLE_C_PREP_WIDTH, TABLE_C_WIDTH, TableCAir};
pub use table_d::{TABLE_D_PREP_WIDTH, TableDAir};
pub use table_e as table_e_mod;
pub use table_e::{TABLE_E_HEIGHT, TABLE_E_WIDTH, TableEAir};
pub use table_f::{TABLE_F_PREP_WIDTH, TABLE_F_WIDTH, TableFAir};

pub use table_a as table_a_mod;
pub use table_b as table_b_mod;
pub use table_c as table_c_mod;
pub use table_d as table_d_mod;
pub use table_f as table_f_mod;
