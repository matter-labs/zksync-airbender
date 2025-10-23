use super::*;

#[test]
fn test_add() {
    test_reg_reg_op(&"add", 0x00000000, 0x00000000, 0x00000000);
    test_reg_reg_op(&"add", 0x00000002, 0x00000001, 0x00000001);
    test_reg_reg_op(&"add", 0x0000000a, 0x00000003, 0x00000007);

    test_reg_reg_op_64(
        &"add",
        0xffffffffffff8000,
        0x0000000000000000,
        0xffffffffffff8000,
    );
    test_reg_reg_op_64(&"add", 0xffffffff80000000, 0xffffffff80000000, 0x00000000);
    test_reg_reg_op_64(
        &"add",
        0xffffffff7fff8000,
        0xffffffff80000000,
        0xffffffffffff8000,
    );
    test_reg_reg_op_64(
        &"add",
        0x0000000000007fff,
        0x0000000000000000,
        0x0000000000007fff,
    );
    test_reg_reg_op_64(
        &"add",
        0x000000007fffffff,
        0x000000007fffffff,
        0x0000000000000000,
    );
    test_reg_reg_op_64(
        &"add",
        0x0000000080007ffe,
        0x000000007fffffff,
        0x0000000000007fff,
    );
    test_reg_reg_op_64(
        &"add",
        0xffffffff80007fff,
        0xffffffff80000000,
        0x0000000000007fff,
    );
    test_reg_reg_op_64(
        &"add",
        0x000000007fff7fff,
        0x000000007fffffff,
        0xffffffffffff8000,
    );
    test_reg_reg_op_64(
        &"add",
        0xffffffffffffffff,
        0x0000000000000000,
        0xffffffffffffffff,
    );
    test_reg_reg_op_64(
        &"add",
        0x0000000000000000,
        0xffffffffffffffff,
        0x0000000000000001,
    );
    test_reg_reg_op_64(
        &"add",
        0xfffffffffffffffe,
        0xffffffffffffffff,
        0xffffffffffffffff,
    );
    test_reg_reg_op_64(
        &"add",
        0x0000000080000000,
        0x0000000000000001,
        0x000000007fffffff,
    );
}
