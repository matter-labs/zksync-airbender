use super::*;

#[test]
fn test_beq() {
    test_branch_op::<true>(&"beq", 0, 0);
    test_branch_op::<true>(&"beq", 1, 1);
    test_branch_op::<true>(&"beq", -1i32 as u32, -1i32 as u32);

    test_branch_op::<false>(&"beq", 0, 1);
    test_branch_op::<false>(&"beq", 1, 0);
    test_branch_op::<false>(&"beq", -1i32 as u32, 1);
    test_branch_op::<false>(&"beq", 1, -1i32 as u32);
}
