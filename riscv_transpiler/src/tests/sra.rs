use super::*;

#[test]
fn test_sltu() {
    test_reg_reg_op_64(&"sra", 0xffffffff80000000, 0xffffffff80000000, 0);
    test_reg_reg_op_64(&"sra", 0xffffffffc0000000, 0xffffffff80000000, 1);
    test_reg_reg_op_64(&"sra", 0xffffffffff000000, 0xffffffff80000000, 7);
    test_reg_reg_op_64(&"sra", 0xfffffffffffe0000, 0xffffffff80000000, 14);
    test_reg_reg_op_64(&"sra", 0xffffffffffffffff, 0xffffffff80000001, 31);
    test_reg_reg_op_64(&"sra", 0x000000007fffffff, 0x000000007fffffff, 0);
    test_reg_reg_op_64(&"sra", 0x000000003fffffff, 0x000000007fffffff, 1);
    test_reg_reg_op_64(&"sra", 0x0000000000ffffff, 0x000000007fffffff, 7);
    test_reg_reg_op_64(&"sra", 0x000000000001ffff, 0x000000007fffffff, 14);
    test_reg_reg_op_64(&"sra", 0x0000000000000000, 0x000000007fffffff, 31);
    test_reg_reg_op_64(&"sra", 0xffffffff81818181, 0xffffffff81818181, 0);
    test_reg_reg_op_64(&"sra", 0xffffffffc0c0c0c0, 0xffffffff81818181, 1);
    test_reg_reg_op_64(&"sra", 0xffffffffff030303, 0xffffffff81818181, 7);
    test_reg_reg_op_64(&"sra", 0xfffffffffffe0606, 0xffffffff81818181, 14);
    test_reg_reg_op_64(&"sra", 0xffffffffffffffff, 0xffffffff81818181, 31);

    // // # Verify that shifts only use bottom six(rv64) or five(rv32) bits

    test_reg_reg_op_64(
        &"sra",
        0xffffffff81818181,
        0xffffffff81818181,
        0xffffffffffffffc0,
    );
    test_reg_reg_op_64(
        &"sra",
        0xffffffffc0c0c0c0,
        0xffffffff81818181,
        0xffffffffffffffc1,
    );
    test_reg_reg_op_64(
        &"sra",
        0xffffffffff030303,
        0xffffffff81818181,
        0xffffffffffffffc7,
    );
    test_reg_reg_op_64(
        &"sra",
        0xfffffffffffe0606,
        0xffffffff81818181,
        0xffffffffffffffce,
    );
    test_reg_reg_op_64(
        &"sra",
        0xffffffffffffffff,
        0xffffffff81818181,
        0xffffffffffffffff,
    );
}
