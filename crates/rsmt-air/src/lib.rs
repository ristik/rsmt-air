//! Table AIRs for the RSMT v6a statement (DEVPLAN M3).
//!
//! Each table's column layout is a `#[repr(C)]` struct (one source of truth for
//! the width) and its AIR is validated with `p3_air::check_constraints` on
//! plan-generated traces — no FRI, no buses yet. LogUp buses and end-to-end
//! proving land in M4.
//!
//! Landed so far: **A** (proof rows), **D** (sorted batch, preprocessed),
//! **E** (byte range), **P** (powers of two). The leaf sponge (**C**), the
//! coherence/junction table (**F**), and the Poseidon2 wrapper (**B**) are the
//! remaining M3 tables (the pre-v6a versions live on disk, unreferenced, as
//! rewrite reference).

mod cols;
pub mod dispatch;
pub mod table_a;
pub mod table_b;
pub mod table_c;
pub mod table_d;
pub mod table_e;
pub mod table_f;
pub mod table_p;
pub mod table_r;

pub use dispatch::RsmtAir;
pub use table_a::{NUM_PUBLIC, TABLE_A_PREP_WIDTH, TABLE_A_WIDTH, TableAAir};
pub use table_b::{P2_VECTOR_LEN, TableBAir};
pub use table_c::{TABLE_C_PREP_WIDTH, TABLE_C_WIDTH, TableCAir};
pub use table_d::{TABLE_D_PREP_WIDTH, TABLE_D_WIDTH, TableDAir};
pub use table_e::{TABLE_E_HEIGHT, TABLE_E_WIDTH, TableEAir};
pub use table_f::{TABLE_F_PREP_WIDTH, TABLE_F_WIDTH, TableFAir};
pub use table_p::{TABLE_P_HEIGHT, TABLE_P_REAL, TABLE_P_WIDTH, TablePAir};
pub use table_r::{TABLE_R_HEIGHT, TABLE_R_WIDTH, TableRAir};
