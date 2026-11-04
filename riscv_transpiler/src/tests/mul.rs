use super::*;

#[test]
fn test_mul() {
    test_reg_reg_op(&"mul", 0x00001200, 0x00007e00, 0xb6db6db7);
    test_reg_reg_op(&"mul", 0x00001240, 0x00007fc0, 0xb6db6db7);
    test_reg_reg_op(&"mul", 0x00000000, 0x00000000, 0x00000000);
    test_reg_reg_op(&"mul", 0x00000001, 0x00000001, 0x00000001);
    test_reg_reg_op(&"mul", 0x00000015, 0x00000003, 0x00000007);
    test_reg_reg_op(&"mul", 0x00000000, 0x00000000, 0xffff8000);
    test_reg_reg_op(&"mul", 0x00000000, 0x80000000, 0x00000000);
    test_reg_reg_op(&"mul", 0x00000000, 0x80000000, 0xffff8000);
    test_reg_reg_op(&"mul", 0x0000ff7f, 0xaaaaaaab, 0x0002fe7d);
    test_reg_reg_op(&"mul", 0x0000ff7f, 0x0002fe7d, 0xaaaaaaab);
    test_reg_reg_op(&"mul", 0x00000000, 0xff000000, 0xff000000);
    test_reg_reg_op(&"mul", 0x00000001, 0xffffffff, 0xffffffff);
    test_reg_reg_op(&"mul", 0xffffffff, 0xffffffff, 0x00000001);
    test_reg_reg_op(&"mul", 0xffffffff, 0x00000001, 0xffffffff);
}
