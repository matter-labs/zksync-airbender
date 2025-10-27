use super::*;

#[test]
fn test_addi() {
    test_reg_imm_op(&"addi", 0x00000000, 0x00000000, 0x000);
    test_reg_imm_op(&"addi", 0x00000002, 0x00000001, 0x001);
    test_reg_imm_op(&"addi", 0x0000000a, 0x00000003, 0x007);

    test_reg_imm_op_64(&"addi", 0xfffffffffffff800, 0x0000000000000000, 0x800);
    test_reg_imm_op_64(&"addi", 0xffffffff80000000, 0xffffffff80000000, 0x000);
    test_reg_imm_op_64(&"addi", 0xffffffff7ffff800, 0xffffffff80000000, 0x800);
    test_reg_imm_op_64(&"addi", 0x00000000000007ff, 0x00000000, 0x7ff);
    test_reg_imm_op_64(&"addi", 0x000000007fffffff, 0x7fffffff, 0x000);
    test_reg_imm_op_64(&"addi", 0x00000000800007fe, 0x7fffffff, 0x7ff);
    test_reg_imm_op_64(&"addi", 0xffffffff800007ff, 0xffffffff80000000, 0x7ff);
    test_reg_imm_op_64(&"addi", 0x000000007ffff7ff, 0x000000007fffffff, 0x800);
    test_reg_imm_op_64(&"addi", 0xffffffffffffffff, 0x0000000000000000, 0xfff);
    test_reg_imm_op_64(&"addi", 0x0000000000000000, 0xffffffffffffffff, 0x001);
    test_reg_imm_op_64(&"addi", 0xfffffffffffffffe, 0xffffffffffffffff, 0xfff);
    test_reg_imm_op_64(&"addi", 0x0000000080000000, 0x7fffffff, 0x001);
}
