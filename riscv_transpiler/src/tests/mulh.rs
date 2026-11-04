use super::*;

#[test]
fn test_mulh() {
    test_reg_reg_op(&"mulh", 0x00000000, 0x00000000, 0x00000000);
    test_reg_reg_op(&"mulh", 0x00000000, 0x00000001, 0x00000001);
    test_reg_reg_op(&"mulh", 0x00000000, 0x00000003, 0x00000007);
    test_reg_reg_op(&"mulh", 0x00000000, 0x00000000, 0xffff8000);
    test_reg_reg_op(&"mulh", 0x00000000, 0x80000000, 0x00000000);
    test_reg_reg_op(&"mulh", 0x00000000, 0x80000000, 0x00000000);
    test_reg_reg_op(&"mulh", 0xffff0081, 0xaaaaaaab, 0x0002fe7d);
    test_reg_reg_op(&"mulh", 0xffff0081, 0x0002fe7d, 0xaaaaaaab);
    test_reg_reg_op(&"mulh", 0x00010000, 0xff000000, 0xff000000);
    test_reg_reg_op(&"mulh", 0x00000000, 0xffffffff, 0xffffffff);
    test_reg_reg_op(&"mulh", 0xffffffff, 0xffffffff, 0x00000001);
    test_reg_reg_op(&"mulh", 0xffffffff, 0x00000001, 0xffffffff);
}
