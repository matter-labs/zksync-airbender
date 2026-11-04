use super::*;

#[test]
fn test_mulhu() {
    test_reg_reg_op(&"mulhu", 0x00000000, 0x00000000, 0x00000000);
    test_reg_reg_op(&"mulhu", 0x00000000, 0x00000001, 0x00000001);
    test_reg_reg_op(&"mulhu", 0x00000000, 0x00000003, 0x00000007);
    test_reg_reg_op(&"mulhu", 0x00000000, 0x00000000, 0xffff8000);
    test_reg_reg_op(&"mulhu", 0x00000000, 0x80000000, 0x00000000);
    test_reg_reg_op(&"mulhu", 0x7fffc000, 0x80000000, 0xffff8000);
    test_reg_reg_op(&"mulhu", 0x0001fefe, 0xaaaaaaab, 0x0002fe7d);
    test_reg_reg_op(&"mulhu", 0x0001fefe, 0x0002fe7d, 0xaaaaaaab);
    test_reg_reg_op(&"mulhu", 0xfe010000, 0xff000000, 0xff000000);
    test_reg_reg_op(&"mulhu", 0xfffffffe, 0xffffffff, 0xffffffff);
    test_reg_reg_op(&"mulhu", 0x00000000, 0xffffffff, 0x00000001);
    test_reg_reg_op(&"mulhu", 0x00000000, 0x00000001, 0xffffffff);
}
