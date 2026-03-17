//! Test suite for 256-bit integer operations with control delegation.
//!
//! Each test case is expressed as a `TestVector`: a pair of `TestInput` (operands + mask)
//! and `ExpectedOutput` (the 8 result limbs + the output flag).
//!
//! Operation masks are built from bit indices defined in `common_constants`:
//!   - bit 0: ADD
//!   - bit 1: SUB
//!   - bit 2: SUB_AND_NEGATE (computes b - a)
//!   - bit 3: MUL_LOW
//!   - bit 4: MUL_HIGH
//!   - bit 5: EQ
//!   - bit 6: CARRY / BORROW-IN
//!   - bit 7: MEMCOPY
use common_constants::delegation_types::bigint_with_control::*;

#[repr(C, align(32))]
pub struct U256(pub [u32; 8]);

pub struct TestInput {
    pub a: [u32; 8],
    pub b: [u32; 8],
    pub mask: u32,
}

pub type ExpectedOutput = [u32; 9];

pub type TestVector = (TestInput, ExpectedOutput);

const fn test_vector(a: [u32; 8], b: [u32; 8], mask: u32, expected: [u32; 9]) -> TestVector {
    (TestInput { a, b, mask }, expected)
}

const fn op(bit: usize) -> u32 {
    1 << bit
}
const fn op_carry(bit: usize) -> u32 {
    (1 << bit) | (1 << CARRY_BIT_IDX)
}

pub const ADD_VECTORS: &[TestVector] = &[
    // Case 1: simple add, no overflow
    test_vector(
        [1, 2, 3, 4, 5, 6, 7, 8],
        [9, 10, 11, 12, 13, 14, 15, 16],
        op(ADD_OP_BIT_IDX),
        [10, 12, 14, 16, 18, 20, 22, 24, 0],
    ),
    // Case 2: single limb carry
    test_vector(
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0, 1, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 3: ripple carry across first 3 limbs
    test_vector(
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 1, 0, 0, 0, 0, 0],
    ),
    // Case 4: full overflow wraps to 0 with carry out
    test_vector(
        [0xFFFF_FFFF; 8],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 5: boundary half range
    test_vector(
        [0x8000_0000, 0, 0, 0, 0, 0, 0, 0],
        [0x8000_0000, 0, 0, 0, 0, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0, 1, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 6: max + max
    test_vector(
        [0xFFFF_FFFF; 8],
        [0xFFFF_FFFF; 8],
        op(ADD_OP_BIT_IDX),
        [0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 7: zeros
    test_vector(
        [0; 8],
        [0; 8],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 8: zero add something
    test_vector(
        [5, 0, 0, 0, 0, 0, 0, 0],
        [0; 8],
        op(ADD_OP_BIT_IDX),
        [5, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 9: mixed carries in the middle limbs
    test_vector(
        [0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0000, 0xFFFF_FFFF, 0x0000_0000, 0x8000_0000, 0x0000_0000],
        [0x1111_1111, 0x2222_2222, 0xFFFF_FFFF, 0x0000_0001, 0x0000_0001, 0xFFFF_FFFF, 0x8000_0000, 0x0000_0000],
        op(ADD_OP_BIT_IDX),
        [0x2345_6789, 0xBCDF_0112, 0x0000_0000, 0x0000_0002, 0x0000_0000, 0x0000_0000, 0x0000_0001, 0x0000_0001, 0],
    ),
    // Case 10: propagate carry through lower 7 limbs, no final overflow
    test_vector(
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x7FFF_FFFF],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0x8000_0000, 0],
    ),
    // Case 11: top limb overflow only
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF],
        [0, 0, 0, 0, 0, 0, 0, 1],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 12: alternating patterns with no carries per limb
    test_vector(
        [0xAAAA_AAAA; 8],
        [0x5555_5555; 8],
        op(ADD_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0],
    ),
    // Case 13: edge carry into second limb only
    test_vector(
        [0xFFFF_FFFE, 0x0000_0000, 0x0000_0001, 0, 0, 0, 0, 0],
        [2, 0, 0, 0, 0, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0x0000_0000, 0x0000_0001, 0x0000_0001, 0, 0, 0, 0, 0, 0],
    ),
    // Case 24: mid-limb exact fill (no carry)
    test_vector(
        [0, 0, 0, 0x7FFF_FFFF, 0, 0, 0, 0],
        [0, 0, 0, 0x8000_0000, 0, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 0xFFFF_FFFF, 0, 0, 0, 0, 0],
    ),
    // Case 25: single mid-limb overflow into next limb only
    test_vector(
        [0, 0, 0, 0, 0xFFFF_FFFF, 0, 0, 0],
        [0, 0, 0, 0, 0x0000_0001, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0x0000_0001, 0, 0, 0],
    ),
    // Case 26: segmented carries
    test_vector(
        [0xFFFF_FFFF, 0, 0xFFFF_FFFF, 0, 0, 0, 0, 0],
        [0x0000_0001, 0, 0x0000_0001, 0, 0, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0, 0x0000_0001, 0, 0x0000_0001, 0, 0, 0, 0, 0],
    ),
    // Case 27: sparse high limbs + big low mask
    test_vector(
        [0, 0, 0, 0, 0, 0, 0x0000_0001, 0x8000_0000],
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0x0000_0001, 0x8000_0000, 0],
    ),
    // Case 28: all limbs 0x8000_0000 + same
    test_vector(
        [0x8000_0000; 8],
        [0x8000_0000; 8],
        op(ADD_OP_BIT_IDX),
        [0, 0x0000_0001, 0x0000_0001, 0x0000_0001, 0x0000_0001, 0x0000_0001, 0x0000_0001, 0x0000_0001, 1],
    ),
    // Case 29: x + (-x) = 0 with carry-out = 1
    test_vector(
        [0xDEAD_BEEF, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006, 0x0000_0007],
        [0x2152_4111, 0xFFFF_FFFE, 0xFFFF_FFFD, 0xFFFF_FFFC, 0xFFFF_FFFB, 0xFFFF_FFFA, 0xFFFF_FFF9, 0xFFFF_FFF8],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 30: max + 2 -> ripple across all lower limbs and set carry-out
    test_vector(
        [0xFFFF_FFFF; 8],
        [0x0000_0002, 0, 0, 0, 0, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0x0000_0001, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 34: mid-limb with carry to next
    test_vector(
        [0, 0, 0, 0, 0, 0x8000_0001, 0, 0],
        [0, 0, 0, 0, 0, 0x8000_0000, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0x0000_0001, 0x0000_0001, 0, 0],
    ),
    // Case 35: limbs sum to all 0xFFFF_FFFF without any carry
    test_vector(
        [0xFFFF_0000; 8],
        [0x0000_FFFF; 8],
        op(ADD_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0],
    ),
    // Case 36: ripple across 4 lower limbs then stop at limb4
    test_vector(
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x1234_5678, 0, 0, 0],
        [0x0000_0001, 0, 0, 0, 0, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0x1234_5679, 0, 0, 0, 0],
    ),
    // Case 37: near-overflow, add 1 into limb0 and limb7
    test_vector(
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE],
        [0x0000_0001, 0, 0, 0, 0, 0, 0, 0x0000_0001],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 38: long ripple + top half+half -> total overflow
    test_vector(
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x7FFF_FFFF],
        [0x0000_0001, 0, 0, 0, 0, 0, 0, 0x8000_0000],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 39: multiple separated carries & exact-fill limbs in one vector
    test_vector(
        [0xFFFF_FFFF, 0, 0x7FFF_FFFF, 0, 0xFFFF_FFFF, 0, 0, 0],
        [0x0000_0001, 0x8000_0000, 0x8000_0000, 0, 0x0000_0001, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0, 0x8000_0001, 0xFFFF_FFFF, 0, 0, 0x0000_0001, 0, 0, 0],
    ),
    // Case 41: high-bit preserved (no carry from low limbs)
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0x8000_0000],
        [5, 0, 0, 0, 0, 0, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0x0000_0005, 0, 0, 0, 0, 0, 0, 0x8000_0000, 0],
    ),
    // Case 42: two adjacent mid-limb carries
    test_vector(
        [0, 0, 0, 0, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0],
        [0, 0, 0, 0, 0x0000_0001, 0x0000_0001, 0, 0],
        op(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0x0000_0001, 0x0000_0001, 0, 0],
    ),
    // Case 43: all F, no overflow
    test_vector(
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x7FFF_FFFF],
        [0, 0, 0, 0, 0, 0, 0, 0x8000_0000],
        op(ADD_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0],
    ),
];

pub const ADD_CARRY_VECTORS: &[TestVector] = &[
    // Case 14: carry-in set. 0xFFFF_FFFE + 1 + carry(1) => 0 with carry out into limb 1
    test_vector(
        [0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op_carry(ADD_OP_BIT_IDX),
        [0, 1, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 15: carry-in, no overflow beyond limb
    test_vector(
        [0; 8],
        [0; 8],
        op_carry(ADD_OP_BIT_IDX),
        [1, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 16: carry-in causes ripple across first 3 limbs
    test_vector(
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0],
        [0; 8],
        op_carry(ADD_OP_BIT_IDX),
        [0, 0, 0, 1, 0, 0, 0, 0, 0],
    ),
    // Case 17: carry-in with boundary half-range
    test_vector(
        [0x8000_0000, 0, 0, 0, 0, 0, 0, 0],
        [0x8000_0000, 0, 0, 0, 0, 0, 0, 0],
        op_carry(ADD_OP_BIT_IDX),
        [1, 1, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 18: carry-in with max + 0
    test_vector(
        [0xFFFF_FFFF; 8],
        [0; 8],
        op_carry(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 19: mixed values with carry-in that does not cause further carries
    test_vector(
        [0x1234_5678, 0x0000_0001, 0, 0, 0, 0, 0, 0],
        [0x0000_0001, 0, 0, 0, 0, 0, 0, 0],
        op_carry(ADD_OP_BIT_IDX),
        [0x1234_567A, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 20: alternating + complement with carry-in all
    test_vector(
        [0xAAAA_AAAA; 8],
        [0x5555_5555; 8],
        op_carry(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 21: top limb overflow due to carry-in only
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF],
        [0; 8],
        op_carry(ADD_OP_BIT_IDX),
        [1, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0],
    ),
    // Case 22: long carry ripple across 7 limbs, increments top to 0x8000_0000, no overflow
    test_vector(
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x7FFF_FFFF],
        [0; 8],
        op_carry(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0x8000_0000, 0],
    ),
    // Case 23: ADD with carry-in where b is max and a is zero
    test_vector(
        [0; 8],
        [0xFFFF_FFFF; 8],
        op_carry(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 31: carry-in ripples through 7 lower limbs
    test_vector(
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x7FFF_FFFF],
        [0; 8],
        op_carry(ADD_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0x8000_0000, 0],
    ),
    // Case 32: carry-in that doesn't propagate
    test_vector(
        [0xFFFF_FFFE, 0xAAAA_AAAA, 0, 0, 0, 0, 0, 0],
        [0; 8],
        op_carry(ADD_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xAAAA_AAAA, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 33: carry-in ripples one limb
    test_vector(
        [0xFFFF_FFFF, 0x1234_5678, 0, 0, 0, 0, 0, 0],
        [0; 8],
        op_carry(ADD_OP_BIT_IDX),
        [0, 0x1234_5679, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 40: carry-in with all 0x8000_0000
    test_vector(
        [0x8000_0000; 8],
        [0; 8],
        op_carry(ADD_OP_BIT_IDX),
        [0x8000_0001, 0x8000_0000, 0x8000_0000, 0x8000_0000, 0x8000_0000, 0x8000_0000, 0x8000_0000, 0x8000_0000, 0],
    ),
];

pub const SUB_VECTORS: &[TestVector] = &[
    // Case 44: simple subtract, no borrow
    test_vector(
        [10, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op(SUB_OP_BIT_IDX),
        [9, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 45: zero minus one -> all F, borrow out
    test_vector(
        [0; 8],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op(SUB_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 46: borrow ripples through first two limbs then stops
    test_vector(
        [0, 0, 1, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op(SUB_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 49: top-limb borrow only
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0x0000_0001],
        op(SUB_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 1],
    ),
    // Case 50: alternating patterns
    test_vector(
        [0xAAAA_AAAA; 8],
        [0x5555_5555; 8],
        op(SUB_OP_BIT_IDX),
        [0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0],
    ),
    // Case 51: equal operands -> zero, no borrow
    test_vector(
        [0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006],
        [0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006],
        op(SUB_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 53: borrow stops at second limb
    test_vector(
        [1, 1, 0, 0, 0, 0, 0, 0],
        [2, 0, 0, 0, 0, 0, 0, 0],
        op(SUB_OP_BIT_IDX),
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 54: all zero
    test_vector(
        [0; 8],
        [0; 8],
        op(SUB_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 55: simple per-limb subtract, no borrows anywhere
    test_vector(
        [10, 20, 30, 40, 50, 60, 70, 80],
        [1, 2, 3, 4, 5, 6, 7, 8],
        op(SUB_OP_BIT_IDX),
        [0x0000_0009, 0x0000_0012, 0x0000_001B, 0x0000_0024, 0x0000_002D, 0x0000_0036, 0x0000_003F, 0x0000_0048, 0],
    ),
    // Case 56: ripple borrow across 3 limbs, then stop
    test_vector(
        [0, 0, 0, 1, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op(SUB_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0],
    ),
    // Case 57: equal numbers => zero, no borrow-out
    test_vector(
        [5, 6, 7, 8, 9, 10, 11, 12],
        [5, 6, 7, 8, 9, 10, 11, 12],
        op(SUB_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 58: identity
    test_vector(
        [5, 0, 0, 0, 0, 0, 0, 0],
        [0; 8],
        op(SUB_OP_BIT_IDX),
        [0x0000_0005, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 59: 0 - 0 = 0, no borrow
    test_vector(
        [0; 8],
        [0; 8],
        op(SUB_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 60: top-limb only underflow
    test_vector(
        [0; 8],
        [0, 0, 0, 0, 0, 0, 0, 1],
        op(SUB_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 1],
    ),
    // Case 44b: exact-fill mid-limb
    test_vector(
        [0, 0, 0, 0x8000_0000, 0, 0, 0, 0],
        [0, 0, 0, 0x8000_0000, 0, 0, 0, 0],
        op(SUB_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 45b: borrow-out=1
    test_vector(
        [0; 8],
        [0xFFFF_FFFF; 8],
        op(SUB_OP_BIT_IDX),
        [0x0000_0001, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 46b: max - max = 0
    test_vector(
        [0xFFFF_FFFF; 8],
        [0xFFFF_FFFF; 8],
        op(SUB_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 47b: long ripple from LSW into top limb
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0x1000_0000],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op(SUB_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x0FFF_FFFF, 0],
    ),
    // Case 61: alternating patterns
    test_vector(
        [0xAAAA_AAAA; 8],
        [0x5555_5555; 8],
        op(SUB_OP_BIT_IDX),
        [0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0],
    ),
    // Case 62: multiple adjacent borrows in the middle
    test_vector(
        [0; 8],
        [1, 1, 0, 0, 1, 1, 0, 0],
        op(SUB_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 67: mixed pattern
    test_vector(
        [0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0000, 0xFFFF_FFFF, 0x0000_0000, 0x8000_0000, 0x0000_0000],
        [0x1111_1111, 0x2222_2222, 0xFFFF_FFFF, 0x0000_0001, 0x0000_0001, 0xFFFF_FFFF, 0x8000_0000, 0x0000_0000],
        op(SUB_OP_BIT_IDX),
        [0x0123_4567, 0x789A_BCCE, 0x0000_0002, 0xFFFF_FFFE, 0xFFFF_FFFD, 0x0000_0001, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 68: high-limb pays for long underflow from LSW
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 1],
        [2, 0, 0, 0, 0, 0, 0, 0],
        op(SUB_OP_BIT_IDX),
        [0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0],
    ),
];

pub const SUB_BORROW_VECTORS: &[TestVector] = &[
    // Case 47: SUB+borrow
    test_vector(
        [2, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op_carry(SUB_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 48: SUB+borrow
    test_vector(
        [0; 8],
        [0; 8],
        op_carry(SUB_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 52: equal operands with borrow-in -> all F, borrow out
    test_vector(
        [0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006],
        [0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006],
        op_carry(SUB_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 63: borrow-in only
    test_vector(
        [5, 0, 0, 0, 0, 0, 0, 0],
        [3, 0, 0, 0, 0, 0, 0, 0],
        op_carry(SUB_OP_BIT_IDX),
        [0x0000_0001, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 64: borrow-in ripples across two zero limbs
    test_vector(
        [0, 0, 1, 0, 0, 0, 0, 0],
        [0; 8],
        op_carry(SUB_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 65: a == b plus borrow-in
    test_vector(
        [0x1234_5678; 8],
        [0x1234_5678; 8],
        op_carry(SUB_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 66: borrow-in stops at top limb
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 1],
        [0; 8],
        op_carry(SUB_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0],
    ),
];

pub const SUB_NEG_VECTORS: &[TestVector] = &[
    // Case 69: simple b > a, no borrow-in
    test_vector(
        [1, 0, 0, 0, 0, 0, 0, 0],
        [10, 0, 0, 0, 0, 0, 0, 0],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [9, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 70: b < a -> underflow wrap to all 0xFFFF_FFFF
    test_vector(
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0; 8],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 71: ripple one limb
    test_vector(
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0, 0, 0],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 74: equal operands
    test_vector(
        [0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6],
        [0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 76: b = max, a = 0 -> result = max
    test_vector(
        [0; 8],
        [0xFFFF_FFFF; 8],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0],
    ),
    // Case 77: b = 0, a = max -> result = 1 with borrow-out
    test_vector(
        [0xFFFF_FFFF; 8],
        [0; 8],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [1, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 78: top limb only
    test_vector(
        [0; 8],
        [0, 0, 0, 0, 0, 0, 0, 1],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 1, 0],
    ),
    // Case 80: b = a + 1 across limb1 boundary
    test_vector(
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
        [0, 0x0000_0001, 0, 0, 0, 0, 0, 0],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0x0000_0001, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 81: b=0, a has LSW and MSW bits set
    test_vector(
        [0x0000_0001, 0, 0, 0, 0, 0, 0, 0x0000_0001],
        [0; 8],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 1],
    ),
    // Case 82: b = all F, a = mixed
    test_vector(
        [0x0123_4567, 0x89AB_CDEF, 0, 0xFFFF_FFFF, 0x8000_0000, 0x7FFF_FFFF, 0, 0x0000_0001],
        [0xFFFF_FFFF; 8],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFEDC_BA98, 0x7654_3210, 0xFFFF_FFFF, 0, 0x7FFF_FFFF, 0x8000_0000, 0xFFFF_FFFF, 0xFFFF_FFFE, 0],
    ),
    // Case 83: exact mid-limb
    test_vector(
        [0, 0, 0, 0x7FFF_FFFF, 0, 0, 0, 0],
        [0, 0, 0, 0x8000_0000, 0, 0, 0, 0],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0, 0, 0, 0x0000_0001, 0, 0, 0, 0, 0],
    ),
    // Case 84: borrow chain: limb5 lends to limb3
    test_vector(
        [0, 0, 0, 0x0000_0002, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0x0000_0001, 0, 0],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0, 0, 0, 0xFFFF_FFFE, 0xFFFF_FFFF, 0, 0, 0, 0],
    ),
    // Case 86: only limb3 differs by +1
    test_vector(
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x1234_5678, 0, 0, 0, 0],
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x1234_5679, 0, 0, 0, 0],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0, 0, 0, 0x0000_0001, 0, 0, 0, 0, 0],
    ),
    // Case 87
    test_vector(
        [0, 0x0000_0001, 0, 0, 0, 0, 0, 0],
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 88
    test_vector(
        [0x1111_1110, 0x2222_2220, 0x3333_3330, 0x4444_4440, 0x5555_5550, 0x6666_6660, 0x7777_7770, 0x8888_8880],
        [0x1111_1115, 0x2222_2225, 0x3333_3335, 0x4444_4445, 0x5555_5555, 0x6666_6665, 0x7777_7775, 0x8888_8885],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [5, 5, 5, 5, 5, 5, 5, 5, 0],
    ),
    // Case 90
    test_vector(
        [0x8000_0000, 0, 0, 0, 0, 0, 0, 0],
        [0; 8],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0x8000_0000, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 91: top-limb underflow only
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0x8000_0000],
        [0, 0, 0, 0, 0, 0, 0, 0x7FFF_FFFF],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 1],
    ),
    // Case 92
    test_vector(
        [0x0000_0001, 0, 0x0000_0001, 0, 0, 0x0000_0001, 0, 0x0000_0001],
        [0; 8],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFE, 1],
    ),
    // Case 94
    test_vector(
        [0x0000_0001, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0x0000_0001, 0, 0, 0, 0],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0],
    ),
    // Case 97
    test_vector(
        [0x0000_0002, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0x0000_0001],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0],
    ),
    // Case 99: b=0 minus mixed a -> complement with borrow-out=1
    test_vector(
        [0xDEAD_BEEF, 0x0000_0001, 0x2222_2222, 0, 0xABCD_EF01, 0x8000_0000, 0, 0xFFFF_FFFF],
        [0; 8],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0x2152_4111, 0xFFFF_FFFE, 0xDDDD_DDDD, 0xFFFF_FFFF, 0x5432_10FE, 0x7FFF_FFFF, 0xFFFF_FFFF, 0, 1],
    ),
    // Case 100
    test_vector(
        [0x8000_0000, 0x0000_0001, 0, 0, 0, 0, 0, 0],
        [0x8000_0000, 0, 0, 0, 0, 0, 0, 0],
        op(SUB_AND_NEGATE_OP_BIT_IDX),
        [0, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
];

pub const SUB_NEG_BORROW_VECTORS: &[TestVector] = &[
    // Case 72
    test_vector(
        [0; 8],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op_carry(SUB_AND_NEGATE_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 73: long ripple from carry-in with a having bit in limb2
    test_vector(
        [0, 0, 1, 0, 0, 0, 0, 0],
        [0; 8],
        op_carry(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 75: equal operands with borrow-in
    test_vector(
        [0x1234_5678; 8],
        [0x1234_5678; 8],
        op_carry(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 79: equal operands with borrow-in (mixed)
    test_vector(
        [0xFFFF_FFFF; 8],
        [0x1111_1111, 0x2222_2222, 0xFFFF_FFFF, 0x0000_0001, 0x0000_0001, 0xFFFF_FFFF, 0x8000_0000, 0],
        op_carry(SUB_AND_NEGATE_OP_BIT_IDX),
        [0x1111_1111, 0x2222_2222, 0xFFFF_FFFF, 0x0000_0001, 0x0000_0001, 0xFFFF_FFFF, 0x8000_0000, 0, 1],
    ),
    // Case 85
    test_vector(
        [0, 0, 0, 0x0000_0002, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0x0000_0001, 0, 0],
        op_carry(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFD, 0xFFFF_FFFF, 0, 0, 0, 0],
    ),
    // Case 89
    test_vector(
        [0; 8],
        [0, 0, 0, 0x0000_0001, 0, 0, 0, 0],
        op_carry(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0],
    ),
    // Case 93
    test_vector(
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
        [0x0000_0001, 0, 0, 0, 0, 0, 0, 0],
        op_carry(SUB_AND_NEGATE_OP_BIT_IDX),
        [0x0000_0001, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 95: complex mixed
    test_vector(
        [0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0, 0xFFFF_FFFF, 0, 0x8000_0000, 0],
        [0x1111_1111, 0x2222_2222, 0xFFFF_FFFF, 0x0000_0001, 0x0000_0001, 0xFFFF_FFFF, 0x8000_0000, 0],
        op_carry(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFEDC_BA98, 0x8765_4331, 0xFFFF_FFFD, 0x0000_0001, 0x0000_0002, 0xFFFF_FFFE, 0, 0, 0],
    ),
    // Case 96: b=0, a=all F -> b - a - 1 == 0, borrow-out=1
    test_vector(
        [0xFFFF_FFFF; 8],
        [0; 8],
        op_carry(SUB_AND_NEGATE_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 98: tiny b < a, plus -1 => underflow to 2^256 - 2
    test_vector(
        [0x0000_0002, 0, 0, 0, 0, 0, 0, 0],
        [0x0000_0001, 0, 0, 0, 0, 0, 0, 0],
        op_carry(SUB_AND_NEGATE_OP_BIT_IDX),
        [0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
];

pub const MUL_LOW_VECTORS: &[TestVector] = &[
    // Case 101: 2 * 3 = 6
    test_vector(
        [2, 0, 0, 0, 0, 0, 0, 0],
        [3, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [6, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 102: 0xFFFF_FFFF * 2
    test_vector(
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
        [2, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0xFFFF_FFFE, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 103: 0x8000_0000 * 0x8000_0000
    test_vector(
        [0x8000_0000, 0, 0, 0, 0, 0, 0, 0],
        [0x8000_0000, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0x4000_0000, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 104: top-limb only (limb7 * limb7)
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 1],
        [0, 0, 0, 0, 0, 0, 0, 1],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 105: all F * 1 -> identity
    test_vector(
        [0xFFFF_FFFF; 8],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0],
    ),
    // Case 106: all F * all F -> low is 1, overflow=1
    test_vector(
        [0xFFFF_FFFF; 8],
        [0xFFFF_FFFF; 8],
        op(MUL_LOW_OP_BIT_IDX),
        [1, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 107: all F * 2
    test_vector(
        [0xFFFF_FFFF; 8],
        [2, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 108: mid-limb multiply (limb3 * limb3)
    test_vector(
        [0, 0, 0, 1, 0, 0, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 1, 0, 0],
    ),
    // Case 109: zero multiplicand
    test_vector(
        [0; 8],
        [0xDEAD_BEEF, 0xCAFE_BABE, 0x0123_4567, 0, 1, 2, 3, 4],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 110: identity by 1 with mixed pattern
    test_vector(
        [0x0000_0001, 0x8000_0000, 0x7FFF_FFFF, 0x0123_4567, 0x89AB_CDEF, 0, 0xFFFF_FFFF, 0x0000_0001],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0x0000_0001, 0x8000_0000, 0x7FFF_FFFF, 0x0123_4567, 0x89AB_CDEF, 0, 0xFFFF_FFFF, 0x0000_0001, 0],
    ),
    // Case 111: cross-limb within boundary (limb1 * limb6)
    test_vector(
        [0, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 1, 0],
    ),
    // Case 112: cross-limb beyond boundary (limb2 * limb6) -> overflow
    test_vector(
        [0, 0, 1, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 113: 0xFFFF_FFFF * 0xFFFF_FFFF
    test_vector(
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0x0000_0001, 0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 114: (a0=1,a1=1) * (b1=1)
    test_vector(
        [1, 1, 0, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 1, 1, 0, 0, 0, 0, 0, 0],
    ),
    // Case 115: doubling multi-limb with carry propagation
    test_vector(
        [0xFFFF_FFFF, 0x0000_0001, 0, 0, 0, 0, 0, 0],
        [2, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0xFFFF_FFFE, 0x0000_0003, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 116: top*low causing high-only carry
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 2],
        [0x8000_0000, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 117: shift by one limb, no overflow
    test_vector(
        [0, 1, 0, 0, 0, 0, 0, 0],
        [0xDEAD_BEEF, 0xCAFE_BABE, 1, 2, 3, 4, 5, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0xDEAD_BEEF, 0xCAFE_BABE, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0],
    ),
    // Case 118: shift by one limb with overflow
    test_vector(
        [0, 1, 0, 0, 0, 0, 0, 0],
        [0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006, 0x0000_0007, 0x0000_0008],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006, 0x0000_0007, 1],
    ),
    // Case 119: mid-limb square (2^64 * 2^64 = 2^128)
    test_vector(
        [0, 0, 1, 0, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 1, 0, 0, 0, 0],
    ),
    // Case 120: exact boundary (2^128 * 2^128 = 2^256) -> overflow
    test_vector(
        [0, 0, 0, 0, 1, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 121
    test_vector(
        [0xFFFF_FFFF; 8],
        [5, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0xFFFF_FFFB, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 122: (-1) * (1 + 2^32)
    test_vector(
        [0xFFFF_FFFF; 8],
        [1, 1, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 123: 0x8000_0000 * 3
    test_vector(
        [0x8000_0000, 0, 0, 0, 0, 0, 0, 0],
        [3, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0x8000_0000, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 124: (1 + 2^32)^2
    test_vector(
        [1, 1, 0, 0, 0, 0, 0, 0],
        [1, 1, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0x0000_0001, 0x0000_0002, 0x0000_0001, 0, 0, 0, 0, 0, 0],
    ),
    // Case 125
    test_vector(
        [0xFFFF_FFFF, 0x0000_0001, 0, 0, 0, 0, 0, 0],
        [2, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0xFFFF_FFFE, 0x0000_0003, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 126: limb6 * limb1
    test_vector(
        [0, 0, 0, 0, 0, 0x0000_0001, 0, 0],
        [0, 0x0000_0001, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0x0000_0001, 0, 0],
    ),
    // Case 127: limb7 * limb1 -> overflow
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0x0000_0001],
        [0, 0x0000_0001, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 128: limb5 * limb2
    test_vector(
        [0, 0, 0, 0, 0, 0x0000_0001, 0, 0],
        [0, 0, 0x0000_0001, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0x0000_0001, 0],
    ),
    // Case 129: limb5 * limb3 -> overflow only
    test_vector(
        [0, 0, 0, 0, 0, 0x0000_0001, 0, 0],
        [0, 0, 0, 0x0000_0001, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 130: (2^32) * (-1)
    test_vector(
        [0, 0x0000_0001, 0, 0, 0, 0, 0, 0],
        [0xFFFF_FFFF; 8],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 131: high-half squares with high 32-bit carry
    test_vector(
        [0, 0, 0, 0x8000_0000, 0, 0, 0, 0],
        [0, 0, 0, 0, 0x8000_0000, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 132: (0x8000_0001)^2
    test_vector(
        [0x8000_0001, 0, 0, 0, 0, 0, 0, 0],
        [0x8000_0001, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0x0000_0001, 0x4000_0001, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 133: 0xFFFF_FFFF * 0x8000_0000
    test_vector(
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
        [0x8000_0000, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0x8000_0000, 0x7FFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 134: 2^128 * 2^97
    test_vector(
        [0, 0, 0, 0, 1, 0, 0, 0],
        [0, 0, 0, 2, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0x0000_0002, 0],
    ),
    // Case 135: 2^224 * 2^32 -> overflow only
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 1],
        [0, 1, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 136: two-limb a * 2
    test_vector(
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0],
        [2, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_LOW_OP_BIT_IDX),
        [0xFFFF_FFFE, 0xFFFF_FFFF, 0x0000_0001, 0, 0, 0, 0, 0, 0],
    ),
];

pub const MUL_HIGH_VECTORS: &[TestVector] = &[
    // Case 137: small * small -> high = 0
    test_vector(
        [2, 0, 0, 0, 0, 0, 0, 0],
        [3, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 138
    test_vector(
        [0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 1, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [1, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 139
    test_vector(
        [0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0],
        [0, 0, 0xFFFF_FFFF, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0x0000_0001, 0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 140
    test_vector(
        [0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, 1],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 1, 0, 0, 0],
    ),
    // Case 141
    test_vector(
        [0, 0, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 1],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0, 0, 0, 1, 0, 0, 0, 0],
    ),
    // Case 142
    test_vector(
        [0, 0, 0, 0, 1, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [1, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 143
    test_vector(
        [0, 0, 0, 0, 0, 0, 1, 0],
        [0, 1, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 144
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 1],
        [0, 0, 1, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 1, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 145
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 1],
        [0, 0, 0, 0, 0, 0, 1, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 1, 0, 0, 0],
    ),
    // Case 146
    test_vector(
        [0, 0, 0, 0, 1, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [1, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 147
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 1],
        [0, 0, 0, 0, 0, 0, 0, 1],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 1, 0, 0],
    ),
    // Case 148
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 1],
        [1, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 149
    test_vector(
        [0, 0, 0, 0xFFFF_FFFF, 0, 0, 0, 0],
        [0, 0, 0, 0, 0xFFFF_FFFF, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 150
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 1],
        [0, 0, 1, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 151
    test_vector(
        [0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0x0000_0001],
        [0, 0xFFFF_FFFF, 0x0000_0001, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFC, 0x0000_0003, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 152
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF],
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0x0000_0001, 0xFFFF_FFFE, 0],
    ),
    // Case 153
    test_vector(
        [0xFFFF_FFFF; 8],
        [0, 1, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 154
    test_vector(
        [0, 0, 0, 0, 0, 0, 0xFFFF_0000, 0],
        [0, 0, 0xFFFF_0000, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0xFFFE_0001, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 155
    test_vector(
        [1, 1, 1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 1, 1, 1, 1],
        op(MUL_HIGH_OP_BIT_IDX),
        [7, 6, 5, 4, 3, 2, 1, 0, 0],
    ),
    // Case 156
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 1],
        [0, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 157
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF],
        [0, 2, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFE, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 158
    test_vector(
        [0, 0, 0, 0, 0, 0x8000_0000, 0, 0],
        [0, 0, 0, 0x8000_0000, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0x4000_0000, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 159
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF],
        [0, 0x0000_0001, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 160
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF],
        [0, 0x0000_0002, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFE, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 161
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0x8000_0000],
        [0, 0x8000_0000, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0x4000_0000, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 162
    test_vector(
        [0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0],
        [0, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 163
    test_vector(
        [0, 0, 0, 0, 0, 0xFFFF_FFFF, 0xFFFF_FFFF, 0],
        [0, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFE, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 164
    test_vector(
        [0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0x0000_0001],
        [0, 0xFFFF_FFFF, 0x0000_0001, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFC, 0x0000_0003, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 165
    test_vector(
        [0xFFFF_FFFF; 8],
        [0, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 166
    test_vector(
        [0, 0, 0, 0, 0, 0, 0xFFFF_0000, 0],
        [0, 0, 0xFFFF_0000, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0xFFFE_0001, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 167
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0x0001_0000],
        [0, 0x0001_0000, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 168
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF],
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0x0000_0001, 0xFFFF_FFFE, 0],
    ),
    // Case 169: mixed pattern
    test_vector(
        [0xFFFF_0001, 0x0000_FFFF, 0x8000_0000, 0x7FFF_FFFF, 0xAAAA_AAAA, 0x5555_5555, 0xDEAD_BEEF, 0xFFFF_FFFF],
        [0, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xDEAD_BEEF, 0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 170
    test_vector(
        [0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0xFFFF_FFFF],
        [0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0xFFFF_FFFF],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0, 0, 0, 0x0000_0001, 0, 0xFFFF_FFFE, 0xFFFF_FFFF, 0],
    ),
    // Case 171
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0x0000_0001],
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF],
        op(MUL_HIGH_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0, 0],
    ),
    // Case 172
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0x8000_0001],
        [0, 0xFFFF_FFFE, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFE, 0x7FFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 173: ALL*ALL => (2^256-1)^2 high half
    test_vector(
        [0xFFFF_FFFF; 8],
        [0xFFFF_FFFF; 8],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0],
    ),
    // Case 174
    test_vector(
        [0xFFFF_FFFF; 8],
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 175
    test_vector(
        [0xFFFF_FFFF; 8],
        [0, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 176
    test_vector(
        [0xFFFF_FFFF; 8],
        [0, 0, 0, 0, 0xFFFF_FFFF, 0, 0, 0],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 0, 0, 0, 0],
    ),
    // Case 177
    test_vector(
        [0xFFFF_FFFF; 8],
        [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF],
        op(MUL_HIGH_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 0],
    ),
];

pub const EQ_VECTORS: &[TestVector] = &[
    // Case 178: zeros equal -> flag=1
    test_vector(
        [0; 8],
        [0; 8],
        op(EQ_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 179: mixed equal pattern -> flag=1
    test_vector(
        [0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6],
        [0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6],
        op(EQ_OP_BIT_IDX),
        [0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6, 1],
    ),
    // Case 180: differ in one limb -> flag=0
    test_vector(
        [0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6],
        [0x1234_5678, 0x9ABC_DEF0, 1, 3, 3, 4, 5, 6],
        op(EQ_OP_BIT_IDX),
        [0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6, 0],
    ),
    // Case 181: all-ones equal -> flag=1
    test_vector(
        [0xFFFF_FFFF; 8],
        [0xFFFF_FFFF; 8],
        op(EQ_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1],
    ),
    // Case 182: max vs zero -> flag=0
    test_vector(
        [0xFFFF_FFFF; 8],
        [0; 8],
        op(EQ_OP_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0],
    ),
    // Case 183: equal with carry bit set -> carry ignored, flag=1
    test_vector(
        [1, 2, 3, 4, 5, 6, 7, 8],
        [1, 2, 3, 4, 5, 6, 7, 8],
        op_carry(EQ_OP_BIT_IDX),
        [1, 2, 3, 4, 5, 6, 7, 8, 1],
    ),
    // Case 184: not equal with carry bit set -> carry ignored, flag=0
    test_vector(
        [1, 2, 3, 4, 5, 6, 7, 8],
        [1, 2, 3, 4, 5, 6, 7, 9],
        op_carry(EQ_OP_BIT_IDX),
        [1, 2, 3, 4, 5, 6, 7, 8, 0],
    ),
    // Case 185: differ only at top limb -> flag=0
    test_vector(
        [0, 0, 0, 0, 0, 0, 0, 0x8000_0000],
        [0, 0, 0, 0, 0, 0, 0, 0x8000_0001],
        op(EQ_OP_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0x8000_0000, 0],
    ),
    // Case 186: equal sparse highs -> flag=1
    test_vector(
        [0, 0, 0, 0x0000_0001, 0, 0x8000_0000, 0, 0],
        [0, 0, 0, 0x0000_0001, 0, 0x8000_0000, 0, 0],
        op(EQ_OP_BIT_IDX),
        [0, 0, 0, 0x0000_0001, 0, 0x8000_0000, 0, 0, 1],
    ),
];

pub const MEMCOPY_VECTORS: &[TestVector] = &[
    // Case 187: basic copy, carry=0 -> out = b, flag=0
    test_vector(
        [0xAAAA_AAAA, 0xBBBB_BBBB, 0xCCCC_CCCC, 0xDDDD_DDDD, 1, 2, 3, 4],
        [0x1111_1111, 0x2222_2222, 0x3333_3333, 0x4444_4444, 5, 6, 7, 8],
        op(MEMCOPY_BIT_IDX),
        [0x1111_1111, 0x2222_2222, 0x3333_3333, 0x4444_4444, 5, 6, 7, 8, 0],
    ),
    // Case 188: MEMCOPY + CARRY: adds 1 to b before copy
    test_vector(
        [0; 8],
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0],
        op_carry(MEMCOPY_BIT_IDX),
        [0, 1, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 189: carry ripples across many limbs
    test_vector(
        [0; 8],
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0],
        op_carry(MEMCOPY_BIT_IDX),
        [0, 0, 1, 0, 0, 0, 0, 0, 0],
    ),
    // Case 190: full overflow when b = all-ones -> wraps to zero, flag=1
    test_vector(
        [0; 8],
        [0xFFFF_FFFF; 8],
        op_carry(MEMCOPY_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
    // Case 191: copy zeros -> zeros, flag=0
    test_vector(
        [0; 8],
        [0; 8],
        op(MEMCOPY_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 192: copy max -> max, flag=0
    test_vector(
        [0; 8],
        [0xFFFF_FFFF; 8],
        op(MEMCOPY_BIT_IDX),
        [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0],
    ),
    // Case 193: increment mixed b, no ripple
    test_vector(
        [0; 8],
        [5, 0x1234_5678, 0, 0, 0, 0, 0, 0],
        op_carry(MEMCOPY_BIT_IDX),
        [6, 0x1234_5678, 0, 0, 0, 0, 0, 0, 0],
    ),
    // Case 194: increment with ripple into top limb only
    test_vector(
        [0; 8],
        [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF],
        op_carry(MEMCOPY_BIT_IDX),
        [0, 1, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0],
    ),
    // Case 195: ensure a is untouched (copy reads from b)
    test_vector(
        [0xDEAD_BEEF, 2, 3, 4, 5, 6, 7, 8],
        [9, 8, 7, 6, 5, 4, 3, 2],
        op(MEMCOPY_BIT_IDX),
        [9, 8, 7, 6, 5, 4, 3, 2, 0],
    ),
    // Case 196: all-ones wrap to zero, flag=1
    test_vector(
        [0xFFFF_FFFF; 8],
        [0xFFFF_FFFF; 8],
        op_carry(MEMCOPY_BIT_IDX),
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
    ),
];

/// Runs all edge-case test vectors across every operation category.
/// For each vector, triggers the CSR delegation with the given inputs and mask,
/// then asserts the result matches the expected output.
pub fn run_edge_case_tests() {
    run_vectors(ADD_VECTORS);
    run_vectors(ADD_CARRY_VECTORS);
    run_vectors(SUB_VECTORS);
    run_vectors(SUB_BORROW_VECTORS);
    run_vectors(SUB_NEG_VECTORS);
    run_vectors(SUB_NEG_BORROW_VECTORS);
    run_vectors(MUL_LOW_VECTORS);
    run_vectors(MUL_HIGH_VECTORS);
    run_vectors(EQ_VECTORS);
    run_vectors(MEMCOPY_VECTORS);
}

fn run_vectors(vectors: &[TestVector]) {
    for (input, expected) in vectors {
        let mut a = U256(input.a);
        let b = U256(input.b);
        let mut out: [u32; 9] = [0; 9];

        let mask = unsafe {
            bigint_csr_trigger_delegation(a.0.as_mut_ptr(), b.0.as_ptr(), input.mask)
        };

        out[0] = a.0[0];
        out[1] = a.0[1];
        out[2] = a.0[2];
        out[3] = a.0[3];
        out[4] = a.0[4];
        out[5] = a.0[5];
        out[6] = a.0[6];
        out[7] = a.0[7];
        out[8] = mask;
        assert_eq!(out, *expected);
    }
}
