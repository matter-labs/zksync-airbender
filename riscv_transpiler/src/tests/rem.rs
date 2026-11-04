use super::*;

#[test]
fn test_rem() {
    test_reg_reg_op(&"rem", 2, 20, 6);
    test_reg_reg_op(&"rem", -2i32 as u32, -20i32 as u32, 6);
    test_reg_reg_op(&"rem", 2, 20, -6i32 as u32);
    test_reg_reg_op(&"rem", -2i32 as u32, -20i32 as u32, -6i32 as u32);
    test_reg_reg_op(&"rem", 0, (-1i32 as u32) << 31, 1);
    test_reg_reg_op(&"rem", 0, (-1i32 as u32) << 31, -1i32 as u32);
    test_reg_reg_op(&"rem", (-1i32 as u32) << 31, (-1i32 as u32) << 31, 0);
    test_reg_reg_op(&"rem", 1, 1, 0);
    test_reg_reg_op(&"rem", 0, 0, 0);
}
