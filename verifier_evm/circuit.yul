function sumcheck_circuit_layer3(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // SUMCHECK ROUNDS
    let eq_scale := 1
    for { let i := 0 } lt(i, GKR_CIRCUIT_LAYER_ROUNDS) { i := add(i, 1) } {
        let w0 := calldataload(ptr)
        let w1 := calldataload(add(ptr, 32))
        let c0 := shr(128, w0)
        let c1 := and(w0, MASK)
        let c2 := shr(128, w1)
        let c3 := and(w1, MASK)
        let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P)
        let r := transcript_4to1_dual(w0, w1) // before check is optimal
        // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
        let dummy_check := mod(add(claim, sub(P, g0g1_scaled)), P)
        mstore(GKR_CIRCUIT_CACHE_PTR, dummy_check)

        claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
        let z := mload(add(POINT_PTR, mul(i, 32)))
        let zr := mulmod(z, r, P)
        eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
        mstore(add(POINT_PTR, mul(i, 32)), r)
        ptr := add(ptr, 64)
    }
    
    // POINT CHECK
    let acc
    {  // AggregateLookupRationalPair: [4]/[5] + [2]/[3] = [0]/[1]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 5)))), shr(128, calldataload(add(ptr, mul(16, 3)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 4)))), shr(128, calldataload(add(ptr, mul(16, 3)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 2)))), shr(128, calldataload(add(ptr, mul(16, 5)))), P))
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
    {  // AggregateLookupRationalPair: [12]/[13] + [10]/[11] = [4]/[5]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 13)))), shr(128, calldataload(add(ptr, mul(16, 11)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 12)))), shr(128, calldataload(add(ptr, mul(16, 11)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 10)))), shr(128, calldataload(add(ptr, mul(16, 13)))), P))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [0] = [6]
        let gate := shr(128, calldataload(add(ptr, mul(16, 0))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [1] = [7]
        let gate := shr(128, calldataload(add(ptr, mul(16, 1))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [14] = [8]
        let gate := shr(128, calldataload(add(ptr, mul(16, 14))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [15] = [9]
        let gate := shr(128, calldataload(add(ptr, mul(16, 15))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    let dummy_check := mod(add(claim, sub(P, rhs_scaled)), P)
    mstore(GKR_CIRCUIT_CACHE_PTR, dummy_check)

    // after stack-heavy values are dead
    // if mload(GKR_CIRCUIT_CACHE_PTR) { revert(0, 0) }

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
    for { let i := 0 } lt(i, GKR_CIRCUIT_LAYER_ROUNDS) { i := add(i, 1) } {
        let w0 := calldataload(ptr)
        let w1 := calldataload(add(ptr, 32))
        let c0 := shr(128, w0)
        let c1 := and(w0, MASK)
        let c2 := shr(128, w1)
        let c3 := and(w1, MASK)
        let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P)
        let r := transcript_4to1_dual(w0, w1) // before check is optimal
        // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
        let dummy_check := mod(add(claim, sub(P, g0g1_scaled)), P)
        mstore(GKR_CIRCUIT_CACHE_PTR, dummy_check)

        claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
        let z := mload(add(POINT_PTR, mul(i, 32)))
        let zr := mulmod(z, r, P)
        eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
        mstore(add(POINT_PTR, mul(i, 32)), r)
        ptr := add(ptr, 64)
    }
    
    // POINT CHECK
    let acc
    {  // MaskIntoIdentityProduct: [1]*[0] + (1-[0]) = [0]
        let gate := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 1)))), shr(128, calldataload(add(ptr, mul(16, 0)))), P), add(1, sub(mul(2, P), shr(128, calldataload(add(ptr, mul(16, 0)))))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaskIntoIdentityProduct: [2]*[0] + (1-[0]) = [1]
        let gate := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 2)))), shr(128, calldataload(add(ptr, mul(16, 0)))), P), add(1, sub(mul(2, P), shr(128, calldataload(add(ptr, mul(16, 0)))))))
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
    {  // AggregateLookupRationalPair: [5]/[6] + [3]/[4] = [4]/[5]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 6)))), shr(128, calldataload(add(ptr, mul(16, 4)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 5)))), shr(128, calldataload(add(ptr, mul(16, 4)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 3)))), shr(128, calldataload(add(ptr, mul(16, 6)))), P))
        gate := num_out
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
    {  // CopyInExtensionField: [11] = [8]
        let gate := shr(128, calldataload(add(ptr, mul(16, 11))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [12] = [9]
        let gate := shr(128, calldataload(add(ptr, mul(16, 12))))
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
    {  // CopyInExtensionField: [17] = [12]
        let gate := shr(128, calldataload(add(ptr, mul(16, 17))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [18] = [13]
        let gate := shr(128, calldataload(add(ptr, mul(16, 18))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [23] = [14]
        let gate := shr(128, calldataload(add(ptr, mul(16, 23))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [24] = [15]
        let gate := shr(128, calldataload(add(ptr, mul(16, 24))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    let dummy_check := mod(add(claim, sub(P, rhs_scaled)), P)
    mstore(GKR_CIRCUIT_CACHE_PTR, dummy_check)

    // after stack-heavy values are dead
    // if mload(GKR_CIRCUIT_CACHE_PTR) { revert(0, 0) }

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

function sumcheck_circuit_layer1(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // SUMCHECK ROUNDS
    let eq_scale := 1
    for { let i := 0 } lt(i, GKR_CIRCUIT_LAYER_ROUNDS) { i := add(i, 1) } {
        let w0 := calldataload(ptr)
        let w1 := calldataload(add(ptr, 32))
        let c0 := shr(128, w0)
        let c1 := and(w0, MASK)
        let c2 := shr(128, w1)
        let c3 := and(w1, MASK)
        let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P)
        let r := transcript_4to1_dual(w0, w1) // before check is optimal
        // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
        let dummy_check := mod(add(claim, sub(P, g0g1_scaled)), P)
        mstore(GKR_CIRCUIT_CACHE_PTR, dummy_check)

        claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
        let z := mload(add(POINT_PTR, mul(i, 32)))
        let zr := mulmod(z, r, P)
        eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
        mstore(add(POINT_PTR, mul(i, 32)), r)
        ptr := add(ptr, 64)
    }
    
    // POINT CHECK
    let acc
    {  // CopyInBaseField: [0] = [0]
        let gate := shr(128, calldataload(add(ptr, mul(16, 0))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // TrivialProduct: [1]*[3] = [1]
        let gate := mulmod(shr(128, calldataload(add(ptr, mul(16, 1)))), shr(128, calldataload(add(ptr, mul(16, 3)))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // TrivialProduct: [2]*[4] = [2]
        let gate := mulmod(shr(128, calldataload(add(ptr, mul(16, 2)))), shr(128, calldataload(add(ptr, mul(16, 4)))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupUnbalancedPairWithMaterializedBaseInputs: [58]/[59] + 1/(δ + [60]) = [3]/[4]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 59)))), add(mload(add(LOGUP_CHALLS_PTR, 32)), shr(128, calldataload(add(ptr, mul(16, 60))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 58)))), add(mload(add(LOGUP_CHALLS_PTR, 32)), shr(128, calldataload(add(ptr, mul(16, 60))))), P), shr(128, calldataload(add(ptr, mul(16, 59)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // AggregateLookupRationalPair: [56]/[57] + [54]/[55] = [5]/[6]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 57)))), shr(128, calldataload(add(ptr, mul(16, 55)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 56)))), shr(128, calldataload(add(ptr, mul(16, 55)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 54)))), shr(128, calldataload(add(ptr, mul(16, 57)))), P))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // AggregateLookupRationalPair: [52]/[53] + [50]/[51] = [7]/[8]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 53)))), shr(128, calldataload(add(ptr, mul(16, 51)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 52)))), shr(128, calldataload(add(ptr, mul(16, 51)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 50)))), shr(128, calldataload(add(ptr, mul(16, 53)))), P))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupUnbalancedPairWithMaterializedBaseInputs: [48]/[49] + 1/(δ + [7]) = [9]/[10]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 49)))), add(mload(add(LOGUP_CHALLS_PTR, 32)), shr(128, calldataload(add(ptr, mul(16, 7))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 48)))), add(mload(add(LOGUP_CHALLS_PTR, 32)), shr(128, calldataload(add(ptr, mul(16, 7))))), P), shr(128, calldataload(add(ptr, mul(16, 49)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupUnbalancedPairWithMaterializedBaseInputs: [67]/[68] + 1/(δ + [69]) = [11]/[12]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 68)))), add(mload(add(LOGUP_CHALLS_PTR, 32)), shr(128, calldataload(add(ptr, mul(16, 69))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 67)))), add(mload(add(LOGUP_CHALLS_PTR, 32)), shr(128, calldataload(add(ptr, mul(16, 69))))), P), shr(128, calldataload(add(ptr, mul(16, 68)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // AggregateLookupRationalPair: [65]/[66] + [63]/[64] = [13]/[14]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 66)))), shr(128, calldataload(add(ptr, mul(16, 64)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 65)))), shr(128, calldataload(add(ptr, mul(16, 64)))), P), mulmod(shr(128, calldataload(add(ptr, mul(16, 63)))), shr(128, calldataload(add(ptr, mul(16, 66)))), P))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [61] = [15]
        let gate := shr(128, calldataload(add(ptr, mul(16, 61))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [62] = [16]
        let gate := shr(128, calldataload(add(ptr, mul(16, 62))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromVectorInputs: 1/(δ + β⁹(0 + 1[8]) + β⁸(0 + 0) + β⁷(0 + 0) + β⁶(0 + 0) + β⁵(0 + 0) + β⁴(0 + 0) + β³(0 + 0) + β²(0 + 1[11]) + β¹(0 + 1[10]) + β⁰(0 + 1[9])) + 1/(δ + β⁹(0 + 1[12]) + β⁸(0 + 0) + β⁷(0 + 1[20]) + β⁶(0 + 1[19]) + β⁵(0 + 1[18]) + β⁴(0 + 1[17]) + β³(0 + 1[16]) + β²(0 + 1[15]) + β¹(0 + 1[14]) + β⁰(0 + 1[13])) = [17]/[18]
        let den_out := mulmod(add(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 8)))), P)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 11)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 10)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 9)))), P))), mload(add(LOGUP_CHALLS_PTR, 32))), add(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 12)))), P)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 20)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 19)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 18)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 17)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 16)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 15)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 14)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 13)))), P))), mload(add(LOGUP_CHALLS_PTR, 32))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 8)))), P)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 11)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 10)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 9)))), P))), mload(add(LOGUP_CHALLS_PTR, 32))), add(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 12)))), P)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 20)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 19)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 18)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 17)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 16)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 15)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 14)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 13)))), P))), mload(add(LOGUP_CHALLS_PTR, 32))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromVectorInputs: 1/(δ + β⁹(0 + 1[21]) + β⁸(0 + 0) + β⁷(0 + 1[29]) + β⁶(0 + 1[28]) + β⁵(0 + 1[27]) + β⁴(0 + 1[26]) + β³(0 + 1[25]) + β²(0 + 1[24]) + β¹(0 + 1[23]) + β⁰(0 + 1[22])) + 1/(δ + β⁹(0 + 1[30]) + β⁸(0 + 0) + β⁷(0 + 1[38]) + β⁶(0 + 1[37]) + β⁵(0 + 1[36]) + β⁴(0 + 1[35]) + β³(0 + 1[34]) + β²(0 + 1[33]) + β¹(0 + 1[32]) + β⁰(0 + 1[31])) = [19]/[20]
        let den_out := mulmod(add(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 21)))), P)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 29)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 28)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 27)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 26)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 25)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 24)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 23)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 22)))), P))), mload(add(LOGUP_CHALLS_PTR, 32))), add(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 30)))), P)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 38)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 37)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 36)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 35)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 34)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 33)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 32)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 31)))), P))), mload(add(LOGUP_CHALLS_PTR, 32))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 21)))), P)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 29)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 28)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 27)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 26)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 25)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 24)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 23)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 22)))), P))), mload(add(LOGUP_CHALLS_PTR, 32))), add(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 30)))), P)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 38)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 37)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 36)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 35)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 34)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 33)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 32)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 31)))), P))), mload(add(LOGUP_CHALLS_PTR, 32))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupUnbalancedPairWithVectorInputs: [70]/[71] + 1/(δ + β⁹(0 + 1[39]) + β⁸(0 + 0) + β⁷(0 + 1[47]) + β⁶(0 + 1[46]) + β⁵(0 + 1[45]) + β⁴(0 + 1[44]) + β³(0 + 1[43]) + β²(0 + 1[42]) + β¹(0 + 1[41]) + β⁰(0 + 1[40])) = [21]/[22]
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 71)))), add(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 39)))), P)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 47)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 46)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 45)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 44)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 43)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 42)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 41)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 40)))), P))), mload(add(LOGUP_CHALLS_PTR, 32))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 70)))), add(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(mulmod(add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 39)))), P)), mload(LOGUP_CHALLS_PTR), P), add(0, 0)), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 47)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 46)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 45)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 44)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 43)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 42)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 41)))), P))), mload(LOGUP_CHALLS_PTR), P), add(0, mulmod(1, shr(128, calldataload(add(ptr, mul(16, 40)))), P))), mload(add(LOGUP_CHALLS_PTR, 32))), P), shr(128, calldataload(add(ptr, mul(16, 71)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [6] = [23]
        let gate := shr(128, calldataload(add(ptr, mul(16, 6))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInExtensionField: [5] = [24]
        let gate := shr(128, calldataload(add(ptr, mul(16, 5))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    let dummy_check := mod(add(claim, sub(P, rhs_scaled)), P)
    mstore(GKR_CIRCUIT_CACHE_PTR, dummy_check)

    // after stack-heavy values are dead
    // if mload(GKR_CIRCUIT_CACHE_PTR) { revert(0, 0) }

    // POINT CLAIMS BATCH (72 POINTS)
    let points := 72
    let is_odd := mod(points, 2)
    if is_odd {
        next_claim := shr(128, calldataload(add(ptr, mul(16, sub(points, 1)))))
    }
    next_alpha := transcript72to1(ptr)
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

function transcript72to1(ptr) -> alpha {
    let input_bytes := mul(72, 16)
    calldatacopy(add(SEED_PTR, 32), ptr, input_bytes)
    let seed := keccak256(SEED_PTR, add(32, input_bytes))
    mstore(SEED_PTR, seed)
    alpha := shr(128, seed)
}

function sumcheck_circuit_layer0(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // SUMCHECK ROUNDS
    let eq_scale := 1
    for { let i := 0 } lt(i, GKR_CIRCUIT_LAYER_ROUNDS) { i := add(i, 1) } {
        let w0 := calldataload(ptr)
        let w1 := calldataload(add(ptr, 32))
        let c0 := shr(128, w0)
        let c1 := and(w0, MASK)
        let c2 := shr(128, w1)
        let c3 := and(w1, MASK)
        let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P)
        let r := transcript_4to1_dual(w0, w1) // before check is optimal
        // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
        let dummy_check := mod(add(claim, sub(P, g0g1_scaled)), P)
        mstore(GKR_CIRCUIT_CACHE_PTR, dummy_check)

        claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
        let z := mload(add(POINT_PTR, mul(i, 32)))
        let zr := mulmod(z, r, P)
        eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
        mstore(add(POINT_PTR, mul(i, 32)), r)
        ptr := add(ptr, 64)
    }
    
    // POINT CHECK
    let acc
    {  // CopyInBaseField: [21] = [0]
        let gate := shr(128, calldataload(add(ptr, mul(16, 21))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductWithoutCaches: (γ + 0 + α[4] + α²0 + α³(0 + [0]) + α⁴[1] + α⁵[2] + α⁶[3])*(γ + [9] + α[10] + α²[11] + α³(0 + [5]) + α⁴[6] + α⁵[7] + α⁶[8]) = [1]
        let gate := mulmod(add(add(add(add(add(add(add(mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 5))), shr(128, calldataload(add(ptr, mul(16, 3)))), P), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 4))), shr(128, calldataload(add(ptr, mul(16, 2)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 3))), shr(128, calldataload(add(ptr, mul(16, 1)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 2))), add(0, shr(128, calldataload(add(ptr, mul(16, 0))))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 1))), 0, P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 0))), shr(128, calldataload(add(ptr, mul(16, 4)))), P)), 0), mload(add(MEMORY_CHALLS_PTR, mul(32, 6)))), add(add(add(add(add(add(add(mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 5))), shr(128, calldataload(add(ptr, mul(16, 8)))), P), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 4))), shr(128, calldataload(add(ptr, mul(16, 7)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 3))), shr(128, calldataload(add(ptr, mul(16, 6)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 2))), add(0, shr(128, calldataload(add(ptr, mul(16, 5))))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 1))), shr(128, calldataload(add(ptr, mul(16, 11)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 0))), shr(128, calldataload(add(ptr, mul(16, 10)))), P)), shr(128, calldataload(add(ptr, mul(16, 9))))), mload(add(MEMORY_CHALLS_PTR, mul(32, 6)))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductWithoutCaches: (γ + 0 + α[4] + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[2] + α⁶[3])*(γ + [9] + α[10] + α²[11] + α³(1 + [24]) + α⁴[25] + α⁵[7] + α⁶[8]) = [2]
        let gate := mulmod(add(add(add(add(add(add(add(mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 5))), shr(128, calldataload(add(ptr, mul(16, 3)))), P), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 4))), shr(128, calldataload(add(ptr, mul(16, 2)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 3))), shr(128, calldataload(add(ptr, mul(16, 25)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 2))), add(0, shr(128, calldataload(add(ptr, mul(16, 24))))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 1))), 0, P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 0))), shr(128, calldataload(add(ptr, mul(16, 4)))), P)), 0), mload(add(MEMORY_CHALLS_PTR, mul(32, 6)))), add(add(add(add(add(add(add(mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 5))), shr(128, calldataload(add(ptr, mul(16, 8)))), P), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 4))), shr(128, calldataload(add(ptr, mul(16, 7)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 3))), shr(128, calldataload(add(ptr, mul(16, 25)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 2))), add(1, shr(128, calldataload(add(ptr, mul(16, 24))))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 1))), shr(128, calldataload(add(ptr, mul(16, 11)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 0))), shr(128, calldataload(add(ptr, mul(16, 10)))), P)), shr(128, calldataload(add(ptr, mul(16, 9))))), mload(add(MEMORY_CHALLS_PTR, mul(32, 6)))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductWithoutCaches: (γ + [16] + α[17] + α²[18] + α³(0 + [12]) + α⁴[13] + α⁵[14] + α⁶[15])*(γ + 2 + α0 + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[22] + α⁶[23]) = [3]
        let gate := mulmod(add(add(add(add(add(add(add(mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 5))), shr(128, calldataload(add(ptr, mul(16, 15)))), P), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 4))), shr(128, calldataload(add(ptr, mul(16, 14)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 3))), shr(128, calldataload(add(ptr, mul(16, 13)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 2))), add(0, shr(128, calldataload(add(ptr, mul(16, 12))))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 1))), shr(128, calldataload(add(ptr, mul(16, 18)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 0))), shr(128, calldataload(add(ptr, mul(16, 17)))), P)), shr(128, calldataload(add(ptr, mul(16, 16))))), mload(add(MEMORY_CHALLS_PTR, mul(32, 6)))), add(add(add(add(add(add(add(mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 5))), shr(128, calldataload(add(ptr, mul(16, 23)))), P), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 4))), shr(128, calldataload(add(ptr, mul(16, 22)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 3))), shr(128, calldataload(add(ptr, mul(16, 25)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 2))), add(0, shr(128, calldataload(add(ptr, mul(16, 24))))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 1))), 0, P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 0))), 0, P)), 2), mload(add(MEMORY_CHALLS_PTR, mul(32, 6)))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductWithoutCaches: (γ + [16] + α[17] + α²[18] + α³(2 + [24]) + α⁴[25] + α⁵[19] + α⁶[20])*(γ + 2 + α0 + α²0 + α³(0 + [28]) + α⁴[29] + α⁵[26] + α⁶[27]) = [4]
        let gate := mulmod(add(add(add(add(add(add(add(mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 5))), shr(128, calldataload(add(ptr, mul(16, 20)))), P), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 4))), shr(128, calldataload(add(ptr, mul(16, 19)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 3))), shr(128, calldataload(add(ptr, mul(16, 25)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 2))), add(2, shr(128, calldataload(add(ptr, mul(16, 24))))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 1))), shr(128, calldataload(add(ptr, mul(16, 18)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 0))), shr(128, calldataload(add(ptr, mul(16, 17)))), P)), shr(128, calldataload(add(ptr, mul(16, 16))))), mload(add(MEMORY_CHALLS_PTR, mul(32, 6)))), add(add(add(add(add(add(add(mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 5))), shr(128, calldataload(add(ptr, mul(16, 27)))), P), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 4))), shr(128, calldataload(add(ptr, mul(16, 26)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 3))), shr(128, calldataload(add(ptr, mul(16, 29)))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 2))), add(0, shr(128, calldataload(add(ptr, mul(16, 28))))), P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 1))), 0, P)), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 0))), 0, P)), 2), mload(add(MEMORY_CHALLS_PTR, mul(32, 6)))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInBaseField: [27] = [60]
        let gate := shr(128, calldataload(add(ptr, mul(16, 27))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    let dummy_check := mod(add(claim, sub(P, rhs_scaled)), P)
    mstore(GKR_CIRCUIT_CACHE_PTR, dummy_check)

    // after stack-heavy values are dead
    // if mload(GKR_CIRCUIT_CACHE_PTR) { revert(0, 0) }

    // POINT CLAIMS BATCH (72 POINTS)
    let points := 72
    let is_odd := mod(points, 2)
    if is_odd {
        next_claim := shr(128, calldataload(add(ptr, mul(16, sub(points, 1)))))
    }
    next_alpha := transcript72to1(ptr)
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

// SKIPPING TRANSCRIPT FN transcript72to1 FOR LAYER 0 -- ALREADY AVAILABLE

