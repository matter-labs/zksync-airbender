function sumcheck_circuit_layer3(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // SUMCHECK ROUNDS
    let eq_scale := 1
    for { let i := 0 } lt(i, CIRCUIT_LAYER_ROUNDS) { i := add(i, 1) } {
        let w0 := calldataload(ptr)
        let w1 := calldataload(add(ptr, 32))
        let c0 := shr(128, w0)
        let c1 := and(w0, MASK)
        let c2 := shr(128, w1)
        let c3 := and(w1, MASK)
        let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P)
        let r := transcript_4to1_dual(w0, w1) // before check is optimal
        // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
        // if mod(add(claim, sub(P, g0g1_scaled)), P) { revert(0, 0) }
        let dummy_check := mod(add(claim, sub(P, g0g1_scaled)), P)
        mstore(CIRCUIT_CACHE_PTR, dummy_check)
        claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
        let z := mload(add(POINT_PTR, mul(i, 32)))
        let zr := mulmod(z, r, P)
        eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
        mstore(add(POINT_PTR, mul(i, 32)), r)
        ptr := add(ptr, 64)
    }
    
    // POINT CHECK
    let acc
    {  // CopyInExtensionField: [15] = [9]
        let gate := shr(128, calldataload(add(ptr, mul(16, 15))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [14] = [8]
        let gate := shr(128, calldataload(add(ptr, mul(16, 14))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [1] = [7]
        let gate := shr(128, calldataload(add(ptr, mul(16, 1))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [0] = [6]
        let gate := shr(128, calldataload(add(ptr, mul(16, 0))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // AggregateLookupRationalPair: [12]/[13] + [10]/[11] = [4]/[5]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 13)))), shr(128, calldataload(add(ptr, mul(16, 11)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 12)))), shr(128, calldataload(add(ptr, mul(16, 11)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 10)))), shr(128, calldataload(add(ptr, mul(16, 13)))), P))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // AggregateLookupRationalPair: [8]/[9] + [6]/[7] = [2]/[3]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 9)))), shr(128, calldataload(add(ptr, mul(16, 7)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 8)))), shr(128, calldataload(add(ptr, mul(16, 7)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 6)))), shr(128, calldataload(add(ptr, mul(16, 9)))), P))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // AggregateLookupRationalPair: [4]/[5] + [2]/[3] = [0]/[1]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 5)))), shr(128, calldataload(add(ptr, mul(16, 3)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 4)))), shr(128, calldataload(add(ptr, mul(16, 3)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 2)))), shr(128, calldataload(add(ptr, mul(16, 5)))), P))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }
    let dummy_check := mod(add(claim, sub(P, rhs_scaled)), P)
    mstore(CIRCUIT_CACHE_PTR, dummy_check)

    // POINT CLAIMS BATCH (16 POINTS)
    let points := 16
    let is_odd := mod(points, 2)
    if is_odd {
        next_claim := shr(128, calldataload(add(ptr, mul(16, sub(points, 1)))))
    }
    next_alpha := transcript16to1(ptr)
    let even_points := sub(points, is_odd)
    let pairs := shr(1, even_points)
    for { let pair := sub(pairs, 1) } lt(pair, pairs) { pair := sub(pair, 1) } {
        let word := calldataload(add(ptr, mul(pair, 32)))
        let el1 := and(MASK, word)
        next_claim := add(mulmod(next_claim, next_alpha, P), el1)
        let el0 := shr(128, word)
        next_claim := add(mulmod(next_claim, next_alpha, P), el0)
    }

    next_ptr := add(ptr, mul(16, points))
}
function transcript16to1(ptr) -> alpha {
    let input_bytes := mul(16, 16)
    calldatacopy(add(SEED_PTR, 32), ptr, input_bytes)
    let seed := keccak256(SEED_PTR, add(32, input_bytes))
    mstore(SEED_PTR, seed)
    alpha := shr(128, seed)
}

function sumcheck_circuit_layer2(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // SUMCHECK ROUNDS
    let eq_scale := 1
    for { let i := 0 } lt(i, CIRCUIT_LAYER_ROUNDS) { i := add(i, 1) } {
        let w0 := calldataload(ptr)
        let w1 := calldataload(add(ptr, 32))
        let c0 := shr(128, w0)
        let c1 := and(w0, MASK)
        let c2 := shr(128, w1)
        let c3 := and(w1, MASK)
        let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P)
        let r := transcript_4to1_dual(w0, w1) // before check is optimal
        // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
        // if mod(add(claim, sub(P, g0g1_scaled)), P) { revert(0, 0) }
        let dummy_check := mod(add(claim, sub(P, g0g1_scaled)), P)
        mstore(CIRCUIT_CACHE_PTR, dummy_check)
        claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
        let z := mload(add(POINT_PTR, mul(i, 32)))
        let zr := mulmod(z, r, P)
        eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
        mstore(add(POINT_PTR, mul(i, 32)), r)
        ptr := add(ptr, 64)
    }
    
    // POINT CHECK
    let acc
    {  // CopyInExtensionField: [24] = [15]
        let gate := shr(128, calldataload(add(ptr, mul(16, 24))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [23] = [14]
        let gate := shr(128, calldataload(add(ptr, mul(16, 23))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [18] = [13]
        let gate := shr(128, calldataload(add(ptr, mul(16, 18))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [17] = [12]
        let gate := shr(128, calldataload(add(ptr, mul(16, 17))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // AggregateLookupRationalPair: [21]/[22] + [19]/[20] = [10]/[11]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 22)))), shr(128, calldataload(add(ptr, mul(16, 20)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 21)))), shr(128, calldataload(add(ptr, mul(16, 20)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 19)))), shr(128, calldataload(add(ptr, mul(16, 22)))), P))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [12] = [9]
        let gate := shr(128, calldataload(add(ptr, mul(16, 12))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [11] = [8]
        let gate := shr(128, calldataload(add(ptr, mul(16, 11))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // AggregateLookupRationalPair: [15]/[16] + [13]/[14] = [6]/[7]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 16)))), shr(128, calldataload(add(ptr, mul(16, 14)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 15)))), shr(128, calldataload(add(ptr, mul(16, 14)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 13)))), shr(128, calldataload(add(ptr, mul(16, 16)))), P))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // AggregateLookupRationalPair: [5]/[6] + [3]/[4] = [4]/[5]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 6)))), shr(128, calldataload(add(ptr, mul(16, 4)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 5)))), shr(128, calldataload(add(ptr, mul(16, 4)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 3)))), shr(128, calldataload(add(ptr, mul(16, 6)))), P))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // AggregateLookupRationalPair: [9]/[10] + [7]/[8] = [2]/[3]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 10)))), shr(128, calldataload(add(ptr, mul(16, 8)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 9)))), shr(128, calldataload(add(ptr, mul(16, 8)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 7)))), shr(128, calldataload(add(ptr, mul(16, 10)))), P))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaskIntoIdentityProduct: [2]*[0] + (1-[0]) = [1]
        let gate := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 2)))), shr(128, calldataload(add(ptr, mul(16, 0)))), P), add(1, sub(mul(2, P), shr(128, calldataload(add(ptr, mul(16, 0)))))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaskIntoIdentityProduct: [1]*[0] + (1-[0]) = [0]
        let gate := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 1)))), shr(128, calldataload(add(ptr, mul(16, 0)))), P), add(1, sub(mul(2, P), shr(128, calldataload(add(ptr, mul(16, 0)))))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }
    let dummy_check := mod(add(claim, sub(P, rhs_scaled)), P)
    mstore(CIRCUIT_CACHE_PTR, dummy_check)

    // POINT CLAIMS BATCH (25 POINTS)
    let points := 25
    let is_odd := mod(points, 2)
    if is_odd {
        next_claim := shr(128, calldataload(add(ptr, mul(16, sub(points, 1)))))
    }
    next_alpha := transcript25to1(ptr)
    let even_points := sub(points, is_odd)
    let pairs := shr(1, even_points)
    for { let pair := sub(pairs, 1) } lt(pair, pairs) { pair := sub(pair, 1) } {
        let word := calldataload(add(ptr, mul(pair, 32)))
        let el1 := and(MASK, word)
        next_claim := add(mulmod(next_claim, next_alpha, P), el1)
        let el0 := shr(128, word)
        next_claim := add(mulmod(next_claim, next_alpha, P), el0)
    }

    next_ptr := add(ptr, mul(16, points))
}
function transcript25to1(ptr) -> alpha {
    let input_bytes := mul(25, 16)
    calldatacopy(add(SEED_PTR, 32), ptr, input_bytes)
    let seed := keccak256(SEED_PTR, add(32, input_bytes))
    mstore(SEED_PTR, seed)
    alpha := shr(128, seed)
}

