//! Test rules for Rust u128 greater than operations

use cvlr::prelude::*;

// Tests for u128 > comparisons

#[rule]
pub fn check_u128_gt_basic() {
    let x: u128 = nondet();
    let y: u128 = nondet();
    let result: bool = x > y;
    clog!(x, y, result);
    cvlr_assert!(result);
}

#[rule]
pub fn check_u128_lt_basic() {
    let x: u128 = nondet();
    let y: u128 = nondet();
    let result: bool = x < y;
    clog!(x, y, result);
    cvlr_assert!(result);
}

#[rule]
pub fn check_u128_gt_verified() {
    let x: u128 = nondet();
    let y: u128 = nondet();

    cvlr_assume!(x > y);

    let result: bool = x > y;
    clog!(x, y, result);
    cvlr_assert!(result);
}


#[rule]
pub fn check_u128_lt_fail() {
    let x: u128 = nondet();
    let y: u128 = nondet();

    cvlr_assume!(x > y);

    let result: bool = x < y;
    clog!(x, y, result);
    cvlr_assert!(result);
}

#[rule]
pub fn check_u128_gt_large_numbers() {
    let x: u128 = nondet();
    let y: u128 = nondet();

    // Testing with values that span both high and low parts
    cvlr_assume!(x > (1u128 << 64) + 100);  // High part = 1, low part = 100
    cvlr_assume!(y < (1u128 << 64) + 100);   // High part = 1, low part = 50
    cvlr_assume!(y > (1u128 << 64) + 50);   // High part = 1, low part = 50

    let result: bool = x > y;
    clog!(x, y, result);
    cvlr_assert!(result);
}

#[rule]
pub fn negative_test_check_u64_gt_basic() {
    let x: u64 = nondet();
    let y: u64 = nondet();
    let result: bool = x > y;
    clog!(x, y, result);
    cvlr_assert!(result);
}


#[rule]
pub fn check_u128_double_branch_simple() {
    let x: u128 = nondet();
    let y: u128 = nondet();
    let z: u128 = nondet();

    if x > y && y > z {
        clog!(x, y, z, "x > y > z path");
        cvlr_assert!(x > z);
    } else {
        clog!(x, y, z, "not x > y > z path");
        cvlr_assert!(!(x > y && y > z));
    }
}
