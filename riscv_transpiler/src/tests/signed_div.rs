use super::*;


// For signed DIV: i32::MIN / -1 must produce quotient = i32::MIN (0x80000000).
// For signed REM: i32::MIN % -1 must produce remainder = 0.

#[test]
fn test_div_signed_overflow_int_min_div_neg1() {
    // i32::MIN / -1 = i32::MIN (overflow wraps)
    test_reg_reg_op_signed(
        "div",
        i32::MIN as u32, // expected quotient = 0x80000000
        i32::MIN as u32, // dividend = -2^31
        -1i32 as u32,    // divisor = -1
    );
}

#[test]
fn test_rem_signed_overflow_int_min_rem_neg1() {
    // i32::MIN % -1 = 0 (remainder is zero on overflow)
    test_reg_reg_op_signed(
        "rem",
        0,                // expected remainder = 0
        i32::MIN as u32,  // dividend = -2^31
        -1i32 as u32,     // divisor = -1
    );
}

// Additional signed division edge cases for completeness
#[test]
fn test_div_signed_by_zero() {
    // RISC-V spec: signed div by zero => quotient = -1 (0xFFFFFFFF)
    test_reg_reg_op_signed("div", 0xFFFF_FFFF, 42, 0);
}

#[test]
fn test_rem_signed_by_zero() {
    // RISC-V spec: signed rem by zero => remainder = dividend
    test_reg_reg_op_signed("rem", 42, 42, 0);
}

#[test]
fn test_div_signed_basic() {
    test_reg_reg_op_signed("div", (-3i32) as u32, 20, (-6i32) as u32);
    test_reg_reg_op_signed("div", 3, (-20i32) as u32, (-6i32) as u32);
    test_reg_reg_op_signed("div", (-3i32) as u32, (-20i32) as u32, 6);
    test_reg_reg_op_signed("div", 3, 20, 6);
}

#[test]
fn test_rem_signed_basic() {
    test_reg_reg_op_signed("rem", 2, 20, 6);
    test_reg_reg_op_signed("rem", (-2i32) as u32, (-20i32) as u32, 6);
    test_reg_reg_op_signed("rem", 2, 20, (-6i32) as u32);
    test_reg_reg_op_signed("rem", (-2i32) as u32, (-20i32) as u32, (-6i32) as u32);
}
