use super::*;

#[test]
fn test_sltu() {
    test_reg_reg_op(&"sltu", 0, 0x00000000, 0x00000000);
    test_reg_reg_op(&"sltu", 0, 0x00000001, 0x00000001);
    test_reg_reg_op(&"sltu", 1, 0x00000003, 0x00000007);
    test_reg_reg_op(&"sltu", 0, 0x00000007, 0x00000003);
    test_reg_reg_op(&"sltu", 1, 0x00000000, 0xffff8000);
    test_reg_reg_op(&"sltu", 0, 0x80000000, 0x00000000);
    test_reg_reg_op(&"sltu", 1, 0x80000000, 0xffff8000);
    test_reg_reg_op(&"sltu", 1, 0x00000000, 0x00007fff);
    test_reg_reg_op(&"sltu", 0, 0x7fffffff, 0x00000000);
    test_reg_reg_op(&"sltu", 0, 0x7fffffff, 0x00007fff);
    test_reg_reg_op(&"sltu", 0, 0x80000000, 0x00007fff);
    test_reg_reg_op(&"sltu", 1, 0x7fffffff, 0xffff8000);
    test_reg_reg_op(&"sltu", 1, 0x00000000, 0xffffffff);
    test_reg_reg_op(&"sltu", 0, 0xffffffff, 0x00000001);
    test_reg_reg_op(&"sltu", 0, 0xffffffff, 0xffffffff);
}
