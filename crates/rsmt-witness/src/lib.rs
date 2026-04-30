//! Trace builder. Lowers an RSMT3 consistency proof (post-order opcode
//! stream) into per-AIR witness rows and per-bus multiplicity tuples.
//!
//! Currently implemented:
//! - Table A row builder (24 witness columns + 3 preprocessed) with
//!   `left_ptr` derived from post-order stack simulation, `old_hash` /
//!   `new_hash` / `old_is_none` filled by running the verifier inline.
//! - Bus 1 (`tree`) multiset balance check (every non-root real row appears
//!   exactly once as a child).

pub mod table_a;
pub mod table_c;
pub mod table_f;

pub use table_a::{TableARow, build_table_a, check_tree_bus_balance};
pub use table_c::{TableCRow, build_table_c};
pub use table_f::{TableFRow, build_table_f};
