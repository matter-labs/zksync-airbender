use super::*;

#[test]
fn test_slt() {
    test_reg_reg_op_64(&"slt", 0, 0x0000000000000000, 0x0000000000000000);
    test_reg_reg_op_64(&"slt", 0, 0x0000000000000001, 0x0000000000000001);
    test_reg_reg_op_64(&"slt", 1, 0x0000000000000003, 0x0000000000000007);
    test_reg_reg_op_64(&"slt", 0, 0x0000000000000007, 0x0000000000000003);
    test_reg_reg_op_64(&"slt", 0, 0x0000000000000000, 0xffffffffffff8000);
    test_reg_reg_op_64(&"slt", 1, 0xffffffff80000000, 0x0000000000000000);
    test_reg_reg_op_64(&"slt", 1, 0xffffffff80000000, 0xffffffffffff8000);
    test_reg_reg_op_64(&"slt", 1, 0x0000000000000000, 0x0000000000007fff);
    test_reg_reg_op_64(&"slt", 0, 0x000000007fffffff, 0x0000000000000000);
    test_reg_reg_op_64(&"slt", 0, 0x000000007fffffff, 0x0000000000007fff);
    test_reg_reg_op_64(&"slt", 1, 0xffffffff80000000, 0x0000000000007fff);
    test_reg_reg_op_64(&"slt", 0, 0x000000007fffffff, 0xffffffffffff8000);
    test_reg_reg_op_64(&"slt", 0, 0x0000000000000000, 0xffffffffffffffff);
    test_reg_reg_op_64(&"slt", 1, 0xffffffffffffffff, 0x0000000000000001);
    test_reg_reg_op_64(&"slt", 0, 0xffffffffffffffff, 0xffffffffffffffff);
}
