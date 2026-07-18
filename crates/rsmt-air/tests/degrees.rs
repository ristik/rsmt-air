//! Symbolic constraint-degree regression (DEVPLAN M3). Pins each table's
//! `max_constraint_degree` to its documented budget so a future edit that
//! raises the degree (and the FRI blowup) fails CI.

use p3_air::{AirLayout, get_max_constraint_degree};
use p3_baby_bear::BabyBear;

use rsmt_air::{
    TABLE_A_PREP_WIDTH, TABLE_A_WIDTH, TABLE_C_PREP_WIDTH, TABLE_C_WIDTH, TABLE_D_PREP_WIDTH,
    TABLE_D_WIDTH, TABLE_F_PREP_WIDTH, TABLE_F_WIDTH, TableAAir, TableCAir, TableDAir, TableEAir,
    TableFAir, TablePAir,
};

fn layout(main: usize, prep: usize, publics: usize) -> AirLayout {
    AirLayout {
        main_width: main,
        preprocessed_width: prep,
        num_public_values: publics,
        ..Default::default()
    }
}

#[test]
fn table_a_degree_is_2() {
    let air = TableAAir::new(8, 5);
    let d = get_max_constraint_degree::<BabyBear, _>(
        &air,
        layout(TABLE_A_WIDTH, TABLE_A_PREP_WIDTH, 17),
    );
    assert_eq!(d, 2, "Table A max degree");
}

#[test]
fn table_c_degree_is_2() {
    let air = TableCAir::new(8, 6, 3);
    let d = get_max_constraint_degree::<BabyBear, _>(
        &air,
        layout(TABLE_C_WIDTH, TABLE_C_PREP_WIDTH, 0),
    );
    assert_eq!(d, 2, "Table C max degree");
}

#[test]
fn table_f_degree_is_3() {
    let air = TableFAir::new(8, 4, 2);
    let d = get_max_constraint_degree::<BabyBear, _>(
        &air,
        layout(TABLE_F_WIDTH, TABLE_F_PREP_WIDTH, 0),
    );
    assert_eq!(d, 3, "Table F max degree");
}

#[test]
fn helper_table_degrees() {
    let d = get_max_constraint_degree::<BabyBear, _>(
        &TableDAir::shape_only(4),
        layout(TABLE_D_WIDTH, TABLE_D_PREP_WIDTH, 0),
    );
    // Canonical reconstruction is gated by is_real → degree 2.
    assert_eq!(d, 2, "Table D degree {d}");

    let e = get_max_constraint_degree::<BabyBear, _>(&TableEAir, layout(1, 1, 0));
    assert!(e <= 1, "Table E degree {e}");

    let p = get_max_constraint_degree::<BabyBear, _>(&TablePAir::default(), layout(1, 3, 0));
    assert_eq!(p, 2, "Table P degree");
}
