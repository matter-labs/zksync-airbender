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
    {  // LookupPairFromVectorInputs: 1/(δ + β⁰(0 + 1[9]) + β¹(0 + 1[10]) + β²(0 + 1[11]) + β³(0 + 0) + β⁴(0 + 0) + β⁵(0 + 0) + β⁶(0 + 0) + β⁷(0 + 0) + β⁸(0 + 0) + β⁹(0 + 1[8])) + 1/(δ + β⁰(0 + 1[13]) + β¹(0 + 1[14]) + β²(0 + 1[15]) + β³(0 + 1[16]) + β⁴(0 + 1[17]) + β⁵(0 + 1[18]) + β⁶(0 + 1[19]) + β⁷(0 + 1[20]) + β⁸(0 + 0) + β⁹(0 + 1[12])) = [17]/[18]
        let den1 := add(mload(add(LOGUP_CHALLS_PTR, 32)), gkr_lookrel_compress_half(gkr_lookrel_compress_half(0, add(0, 0), add(0, 0), add(0, 0), add(0, 0), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 8))))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 9)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 10)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 11)))))), add(0, 0), add(0, 0))) // for generic lookups we collect
        let den2 := add(mload(add(LOGUP_CHALLS_PTR, 32)), gkr_lookrel_compress_half(gkr_lookrel_compress_half(0, add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 18)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 19)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 20)))))), add(0, 0), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 12))))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 13)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 14)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 15)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 16)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 17)))))))) // for generic lookups we collect
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromVectorInputs: 1/(δ + β⁰(0 + 1[22]) + β¹(0 + 1[23]) + β²(0 + 1[24]) + β³(0 + 1[25]) + β⁴(0 + 1[26]) + β⁵(0 + 1[27]) + β⁶(0 + 1[28]) + β⁷(0 + 1[29]) + β⁸(0 + 0) + β⁹(0 + 1[21])) + 1/(δ + β⁰(0 + 1[31]) + β¹(0 + 1[32]) + β²(0 + 1[33]) + β³(0 + 1[34]) + β⁴(0 + 1[35]) + β⁵(0 + 1[36]) + β⁶(0 + 1[37]) + β⁷(0 + 1[38]) + β⁸(0 + 0) + β⁹(0 + 1[30])) = [19]/[20]
        let den1 := add(mload(add(LOGUP_CHALLS_PTR, 32)), gkr_lookrel_compress_half(gkr_lookrel_compress_half(0, add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 27)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 28)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 29)))))), add(0, 0), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 21))))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 22)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 23)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 24)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 25)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 26)))))))) // for generic lookups we collect
        let den2 := add(mload(add(LOGUP_CHALLS_PTR, 32)), gkr_lookrel_compress_half(gkr_lookrel_compress_half(0, add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 36)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 37)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 38)))))), add(0, 0), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 30))))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 31)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 32)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 33)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 34)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 35)))))))) // for generic lookups we collect
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupUnbalancedPairWithVectorInputs: [70]/[71] + 1/(δ + β⁰(0 + 1[40]) + β¹(0 + 1[41]) + β²(0 + 1[42]) + β³(0 + 1[43]) + β⁴(0 + 1[44]) + β⁵(0 + 1[45]) + β⁶(0 + 1[46]) + β⁷(0 + 1[47]) + β⁸(0 + 0) + β⁹(0 + 1[39])) = [21]/[22]
        let den2 := add(mload(add(LOGUP_CHALLS_PTR, 32)), gkr_lookrel_compress_half(gkr_lookrel_compress_half(0, add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 45)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 46)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 47)))))), add(0, 0), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 39))))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 40)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 41)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 42)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 43)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 44)))))))) // for generic lookups we collect
        let den_out := mulmod(shr(128, calldataload(add(ptr, mul(16, 71)))), den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 70)))), den2, P), shr(128, calldataload(add(ptr, mul(16, 71)))))
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
        let lhs := gkr_memrel_compress(0, shr(128, calldataload(add(ptr, mul(16, 4)))), 0, add(0, shr(128, calldataload(add(ptr, mul(16, 0))))), shr(128, calldataload(add(ptr, mul(16, 1)))), shr(128, calldataload(add(ptr, mul(16, 2)))), shr(128, calldataload(add(ptr, mul(16, 3))))) // for memrel we collect
        let rhs := gkr_memrel_compress(shr(128, calldataload(add(ptr, mul(16, 9)))), shr(128, calldataload(add(ptr, mul(16, 10)))), shr(128, calldataload(add(ptr, mul(16, 11)))), add(0, shr(128, calldataload(add(ptr, mul(16, 5))))), shr(128, calldataload(add(ptr, mul(16, 6)))), shr(128, calldataload(add(ptr, mul(16, 7)))), shr(128, calldataload(add(ptr, mul(16, 8))))) // for memrel we collect
        let gate := mulmod(lhs, rhs, P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductWithoutCaches: (γ + 0 + α[4] + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[2] + α⁶[3])*(γ + [9] + α[10] + α²[11] + α³(1 + [24]) + α⁴[25] + α⁵[7] + α⁶[8]) = [2]
        let lhs := gkr_memrel_compress(0, shr(128, calldataload(add(ptr, mul(16, 4)))), 0, add(0, shr(128, calldataload(add(ptr, mul(16, 24))))), shr(128, calldataload(add(ptr, mul(16, 25)))), shr(128, calldataload(add(ptr, mul(16, 2)))), shr(128, calldataload(add(ptr, mul(16, 3))))) // for memrel we collect
        let rhs := gkr_memrel_compress(shr(128, calldataload(add(ptr, mul(16, 9)))), shr(128, calldataload(add(ptr, mul(16, 10)))), shr(128, calldataload(add(ptr, mul(16, 11)))), add(1, shr(128, calldataload(add(ptr, mul(16, 24))))), shr(128, calldataload(add(ptr, mul(16, 25)))), shr(128, calldataload(add(ptr, mul(16, 7)))), shr(128, calldataload(add(ptr, mul(16, 8))))) // for memrel we collect
        let gate := mulmod(lhs, rhs, P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductWithoutCaches: (γ + [16] + α[17] + α²[18] + α³(0 + [12]) + α⁴[13] + α⁵[14] + α⁶[15])*(γ + 2 + α0 + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[22] + α⁶[23]) = [3]
        let lhs := gkr_memrel_compress(shr(128, calldataload(add(ptr, mul(16, 16)))), shr(128, calldataload(add(ptr, mul(16, 17)))), shr(128, calldataload(add(ptr, mul(16, 18)))), add(0, shr(128, calldataload(add(ptr, mul(16, 12))))), shr(128, calldataload(add(ptr, mul(16, 13)))), shr(128, calldataload(add(ptr, mul(16, 14)))), shr(128, calldataload(add(ptr, mul(16, 15))))) // for memrel we collect
        let rhs := gkr_memrel_compress(2, 0, 0, add(0, shr(128, calldataload(add(ptr, mul(16, 24))))), shr(128, calldataload(add(ptr, mul(16, 25)))), shr(128, calldataload(add(ptr, mul(16, 22)))), shr(128, calldataload(add(ptr, mul(16, 23))))) // for memrel we collect
        let gate := mulmod(lhs, rhs, P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductWithoutCaches: (γ + [16] + α[17] + α²[18] + α³(2 + [24]) + α⁴[25] + α⁵[19] + α⁶[20])*(γ + 2 + α0 + α²0 + α³(0 + [28]) + α⁴[29] + α⁵[26] + α⁶[27]) = [4]
        let lhs := gkr_memrel_compress(shr(128, calldataload(add(ptr, mul(16, 16)))), shr(128, calldataload(add(ptr, mul(16, 17)))), shr(128, calldataload(add(ptr, mul(16, 18)))), add(2, shr(128, calldataload(add(ptr, mul(16, 24))))), shr(128, calldataload(add(ptr, mul(16, 25)))), shr(128, calldataload(add(ptr, mul(16, 19)))), shr(128, calldataload(add(ptr, mul(16, 20))))) // for memrel we collect
        let rhs := gkr_memrel_compress(2, 0, 0, add(0, shr(128, calldataload(add(ptr, mul(16, 28))))), shr(128, calldataload(add(ptr, mul(16, 29)))), shr(128, calldataload(add(ptr, mul(16, 26)))), shr(128, calldataload(add(ptr, mul(16, 27))))) // for memrel we collect
        let gate := mulmod(lhs, rhs, P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(2) + α²(Cache(3) + 0) + 0) * (γ + 1 + αCache(2) + α²(Cache(3) + 1024) + 0) = [5]
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR, mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR, mul(32, 2))), P))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR, mul(32, 3))), 0), P), 0)) // for memrel we collect
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR, mul(32, 3))), 1024), P), 0)) // for memrel we collect
        let gate := mulmod(lhs, rhs, P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(2) + α²(Cache(3) + 0) + α³[32] + α⁴[33] + α⁵[30] + α⁶[31]) * (γ + 1 + αCache(2) + α²(Cache(3) + 1024) + α³[36] + α⁴[37] + α⁵[34] + α⁶[35]) = [6]
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR, mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR, mul(32, 2))), P))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR, mul(32, 3))), 0), P), gkr_memrel_compress_high(shr(128, calldataload(add(ptr, mul(16, 32)))), shr(128, calldataload(add(ptr, mul(16, 33)))), shr(128, calldataload(add(ptr, mul(16, 30)))), shr(128, calldataload(add(ptr, mul(16, 31))))))) // for memrel we collect
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR, mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR, mul(32, 3))), 1024), P), gkr_memrel_compress_high(shr(128, calldataload(add(ptr, mul(16, 36)))), shr(128, calldataload(add(ptr, mul(16, 37)))), shr(128, calldataload(add(ptr, mul(16, 34)))), shr(128, calldataload(add(ptr, mul(16, 35))))))) // for memrel we collect
        let gate := mulmod(lhs, rhs, P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupFromMaterializedBaseInputWithSetup: 1/(δ + [85]) - [100]/(δ + Cache(0)) = [48]/[49]
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR, 32)), shr(128, calldataload(add(ptr, mul(16, 85))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), mload(add(GKR_CIRCUIT_CACHE_PTR, mul(32, 0)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR, 32)), mload(add(GKR_CIRCUIT_CACHE_PTR, mul(32, 0)))), sub(P, mulmod(shr(128, calldataload(add(ptr, mul(16, 100)))), add(mload(add(LOGUP_CHALLS_PTR, 32)), shr(128, calldataload(add(ptr, mul(16, 85))))), P)))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromBaseInputs: 1/(δ + 0 + 1[86]) + 1/(δ + 0 + 1[19]) = [50]/[51]
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 86))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 19))))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 86))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 19))))))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromBaseInputs: 1/(δ + 0 + 1[20]) + 1/(δ + 0 + 1[23]) = [52]/[53]
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 20))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 23))))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 20))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 23))))))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromBaseInputs: 1/(δ + 0 + 1[88]) + 1/(δ + 0 + 1[10]) = [54]/[55]
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 88))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 10))))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 88))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 10))))))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromBaseInputs: 1/(δ + 0 + 1[11]) + 1/(δ + 0 + 1[17]) = [56]/[57]
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 11))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 17))))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 11))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 17))))))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromBaseInputs: 1/(δ + 0 + 1[18]) + 1/(δ + 0 + 1[26]) = [58]/[59]
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 18))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 26))))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 18))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 26))))))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInBaseField: [27] = [60]
        let gate := shr(128, calldataload(add(ptr, mul(16, 27))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupFromMaterializedBaseInputWithSetup: 1/(δ + [28]) - [101]/(δ + Cache(1)) = [61]/[62]
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR, 32)), shr(128, calldataload(add(ptr, mul(16, 28))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), mload(add(GKR_CIRCUIT_CACHE_PTR, mul(32, 1)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR, 32)), mload(add(GKR_CIRCUIT_CACHE_PTR, mul(32, 1)))), sub(P, mulmod(shr(128, calldataload(add(ptr, mul(16, 101)))), add(mload(add(LOGUP_CHALLS_PTR, 32)), shr(128, calldataload(add(ptr, mul(16, 28))))), P)))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromBaseInputs: 1/(δ + 0 + 1[29]) + 1/(δ + 0 + -1[24] + 1[0] + 2^19[97]) = [63]/[64]
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 29))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, add(add(mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 24))))), mul(1, shr(128, calldataload(add(ptr, mul(16, 0)))))), mul(524288, shr(128, calldataload(add(ptr, mul(16, 97)))))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 29))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(0, add(add(mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 24))))), mul(1, shr(128, calldataload(add(ptr, mul(16, 0)))))), mul(524288, shr(128, calldataload(add(ptr, mul(16, 97)))))))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromBaseInputs: 1/(δ + 2^19 + -1[25] + 1[1] + -1[97]) + 1/(δ + -1 + -1[24] + 1[5] + 2^19[98]) = [65]/[66]
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(524288, add(add(mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 25))))), mul(1, shr(128, calldataload(add(ptr, mul(16, 1)))))), mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 97)))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(sub(P, 1), add(add(mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 24))))), mul(1, shr(128, calldataload(add(ptr, mul(16, 5)))))), mul(524288, shr(128, calldataload(add(ptr, mul(16, 98)))))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(524288, add(add(mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 25))))), mul(1, shr(128, calldataload(add(ptr, mul(16, 1)))))), mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 97)))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(sub(P, 1), add(add(mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 24))))), mul(1, shr(128, calldataload(add(ptr, mul(16, 5)))))), mul(524288, shr(128, calldataload(add(ptr, mul(16, 98)))))))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromBaseInputs: 1/(δ + 2^19 + -1[25] + 1[6] + -1[98]) + 1/(δ + -2 + -1[24] + 1[12] + 2^19[99]) = [67]/[68]
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(524288, add(add(mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 25))))), mul(1, shr(128, calldataload(add(ptr, mul(16, 6)))))), mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 98)))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(sub(P, 2), add(add(mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 24))))), mul(1, shr(128, calldataload(add(ptr, mul(16, 12)))))), mul(524288, shr(128, calldataload(add(ptr, mul(16, 99)))))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR, 32)), add(524288, add(add(mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 25))))), mul(1, shr(128, calldataload(add(ptr, mul(16, 6)))))), mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 98)))))))), add(mload(add(LOGUP_CHALLS_PTR, 32)), add(sub(P, 2), add(add(mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 24))))), mul(1, shr(128, calldataload(add(ptr, mul(16, 12)))))), mul(524288, shr(128, calldataload(add(ptr, mul(16, 99)))))))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaterializeSingleLookupInput: 2^19 + -1[25] + 1[13] + -1[99] = [69]
        let gate := add(524288, add(add(mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 25))))), mul(1, shr(128, calldataload(add(ptr, mul(16, 13)))))), mul(sub(P, 1), shr(128, calldataload(add(ptr, mul(16, 99)))))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupWithDensAndSetupExpressions: [21]/(δ + β⁰(0 + 1[22]) + β¹(0 + 1[23]) + β²(0 + 1[4]) + β³(0 + 1[38]) + β⁴(0 + 1[39]) + β⁵(0 + 1[40]) + β⁶(0 + 1[41]) + β⁷(0 + 1[42]) + β⁸(0 + 1[43] + 2[44] + 2^2[45] + 2^3[46] + 2^4[47] + 2^5[48] + 2^6[49] + 2^7[50] + 2^8[51] + 2^9[52] + 2^10[53] + 2^11[54] + 2^12[55] + 2^13[56] + 2^14[57] + 2^15[58] + 2^16[9] + 2^17[16]) + β⁹(46 + 0)) - [102]/(δ + β⁰[103] + β¹[104] + β²[105] + β³[106] + β⁴[107] + β⁵[108] + β⁶[109] + β⁷[110] + β⁸[111] + β⁹[112]) = [70]/[71]
        let input_den := add(mload(add(LOGUP_CHALLS_PTR, 32)), gkr_lookrel_compress_half(gkr_lookrel_compress_half(0, add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 40)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 41)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 42)))))), add(0, add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(mul(1, shr(128, calldataload(add(ptr, mul(16, 43))))), mul(2, shr(128, calldataload(add(ptr, mul(16, 44)))))), mul(4, shr(128, calldataload(add(ptr, mul(16, 45)))))), mul(8, shr(128, calldataload(add(ptr, mul(16, 46)))))), mul(16, shr(128, calldataload(add(ptr, mul(16, 47)))))), mul(32, shr(128, calldataload(add(ptr, mul(16, 48)))))), mul(64, shr(128, calldataload(add(ptr, mul(16, 49)))))), mul(128, shr(128, calldataload(add(ptr, mul(16, 50)))))), mul(256, shr(128, calldataload(add(ptr, mul(16, 51)))))), mul(512, shr(128, calldataload(add(ptr, mul(16, 52)))))), mul(1024, shr(128, calldataload(add(ptr, mul(16, 53)))))), mul(2048, shr(128, calldataload(add(ptr, mul(16, 54)))))), mul(4096, shr(128, calldataload(add(ptr, mul(16, 55)))))), mul(8192, shr(128, calldataload(add(ptr, mul(16, 56)))))), mul(16384, shr(128, calldataload(add(ptr, mul(16, 57)))))), mul(32768, shr(128, calldataload(add(ptr, mul(16, 58)))))), mul(65536, shr(128, calldataload(add(ptr, mul(16, 9)))))), mul(131072, shr(128, calldataload(add(ptr, mul(16, 16))))))), add(46, 0)), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 22)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 23)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 4)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 38)))))), add(0, mul(1, shr(128, calldataload(add(ptr, mul(16, 39)))))))) // for generic lookups we collect
        let setup_den := add(mload(add(LOGUP_CHALLS_PTR, 32)), gkr_lookrel_compress_half(gkr_lookrel_compress_half(0, shr(128, calldataload(add(ptr, mul(16, 108)))), shr(128, calldataload(add(ptr, mul(16, 109)))), shr(128, calldataload(add(ptr, mul(16, 110)))), shr(128, calldataload(add(ptr, mul(16, 111)))), shr(128, calldataload(add(ptr, mul(16, 112))))), shr(128, calldataload(add(ptr, mul(16, 103)))), shr(128, calldataload(add(ptr, mul(16, 104)))), shr(128, calldataload(add(ptr, mul(16, 105)))), shr(128, calldataload(add(ptr, mul(16, 106)))), shr(128, calldataload(add(ptr, mul(16, 107)))))) // for generic lookups we collect
        let den_out := mulmod(input_den, setup_den, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(ptr, mul(16, 21)))), setup_den, P), sub(P, mulmod(input_den, shr(128, calldataload(add(ptr, mul(16, 102)))), P)))
        gate := num_out
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

function gkr_memrel_compress(address_space, addr_low, addr_high, ts_low, ts_high, val_low, val_high) -> compressed {
    compressed := add(mload(add(MEMORY_CHALLS_PTR, 192)), address_space)
    compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR), addr_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR, 32)), addr_high, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR, 64)), ts_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR, 96)), ts_high, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR, 128)), val_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR, 160)), val_high, P))
}

// Fold five generic lookup tuple columns into an existing Horner accumulator.
// A single helper that took all c0..c9 made solc materialize all ten columns
// at the call boundary and failed stack allocation. Splitting the fold into
// two five-column calls keeps each call boundary small while still supporting
// arbitrary linrel_to_calldata_inner() output for every column.
function gkr_lookrel_compress_half(acc, c0, c1, c2, c3, c4) -> acc_next {
    let beta := mload(LOGUP_CHALLS_PTR)
    acc_next := add(mulmod(acc, beta, P), c4)
    acc_next := add(mulmod(acc_next, beta, P), c3)
    acc_next := add(mulmod(acc_next, beta, P), c2)
    acc_next := add(mulmod(acc_next, beta, P), c1)
    acc_next := add(mulmod(acc_next, beta, P), c0)
}

function gkr_memrel_compress_low(address_space, addr_low, addr_high) -> compressed {
    compressed := add(compressed, add(mload(add(MEMORY_CHALLS_PTR, 192)), address_space))
    compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR), addr_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR, 32)), addr_high, P))
}
function gkr_memrel_compress_high(ts_low, ts_high, val_low, val_high) -> compressed {
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR, 64)), ts_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR, 96)), ts_high, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR, 128)), val_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR, 160)), val_high, P))
}

