use super::{run_test_vector_cases, TestVectorSpec};

const SELECTED_TEST_VECTORS: &[usize] = &[0, 1, 4, 5, 20, 169];

#[test]
fn test_vector_beq() {
    run_test_vector_cases(TestVectorSpec {
        test_vectors: include_str!("data/beq-01.S"),
        match_prefix: "TEST_BRANCH_OP",
        patch_match: None,
        opfields: &[0, 2, 3, 6],
        patch_immediate: Some(6),
        patch_immediate_with_register: false,
        initial_registers_index: &[(2, 4), (3, 5)],
        patch_initial_register: None,
        final_register_index: Some((2, 4)),
        selected_test_vectors: SELECTED_TEST_VECTORS,
    });
}
