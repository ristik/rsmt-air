//! Column-layout helpers. Each table's column layout is a single `#[repr(C)]`
//! struct of `T` fields (one source of truth for the width). [`cast`]
//! reinterprets a trace row `&[T]` as `&Cols<T>`; [`width_of`] recovers the
//! column count from the struct size.

/// Reinterpret a trace row as a typed column struct. The row length must equal
/// the struct's field count (checked in debug via `align_to`).
#[inline]
pub(crate) fn cast<T, C>(row: &[T]) -> &C {
    // Safe: `C` is `#[repr(C)]` over `T` fields, so it has the same alignment as
    // `T` and a size of `width_of::<C>()` elements; a full-width row aligns
    // exactly to one `C`.
    let (prefix, body, suffix) = unsafe { row.align_to::<C>() };
    assert!(prefix.is_empty(), "column cast: misaligned prefix");
    assert!(suffix.is_empty(), "column cast: trailing elements");
    assert_eq!(body.len(), 1, "column cast: row width mismatch");
    &body[0]
}

/// Number of `T`-columns in a `#[repr(C)]` layout struct `C<u8>`, i.e.
/// `size_of::<C<u8>>()` (each field is a `u8` or `[u8; k]`, align 1, no
/// padding).
pub const fn width_of<C>() -> usize {
    core::mem::size_of::<C>()
}
