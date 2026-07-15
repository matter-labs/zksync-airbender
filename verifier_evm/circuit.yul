function sumcheck_circuit_layer3(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl3(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc
            mstore(CIRCUIT_PTR, ptr)
            scl3_caches()
            acc := scl3_g0(alpha, acc)
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }

    
            // WRITEBACK claims for next layer (16 evals)
                for { let wk := 0 } lt(wk, 16) { wk := add(wk, 1) } {
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk)))))
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // split the absorb: final_step, draw, extras). next_claim unused (sccl recomputes).
    next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, 16)
}

            function scl3_caches() {
            }
            function scl3_g0(alpha, a) -> acc { acc := a
    // CopyInExtensionField: [15] = 9
    acc := gate_copyinextensionfield(alpha, acc, 15)
    
    // CopyInExtensionField: [14] = 8
    acc := gate_copyinextensionfield(alpha, acc, 14)
    
    // CopyInExtensionField: [1] = 7
    acc := gate_copyinextensionfield(alpha, acc, 1)
    
    // CopyInExtensionField: [0] = 6
    acc := gate_copyinextensionfield(alpha, acc, 0)
    
    // AggregateLookupRationalPair: [12]/[13] + [10]/[11] = 4/5
    acc := gate_aggregatelookuprationalpair(alpha, acc, 12, 10, 13, 11)
    
    // AggregateLookupRationalPair: [8]/[9] + [6]/[7] = 2/3
    acc := gate_aggregatelookuprationalpair(alpha, acc, 8, 6, 9, 7)
    
    // AggregateLookupRationalPair: [4]/[5] + [2]/[3] = 0/1
    acc := gate_aggregatelookuprationalpair(alpha, acc, 4, 2, 5, 3)
    
            }
            function sccl3(alpha) -> claim {
            let src := GKR_CLAIMS_PTR()
            claim := 0
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 0))))
            }
function sumcheck_circuit_layer2(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl2(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc
            mstore(CIRCUIT_PTR, ptr)
            scl2_caches()
            acc := scl2_g0(alpha, acc)
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }

    
            // WRITEBACK claims for next layer (25 evals)
                for { let wk := 0 } lt(wk, 25) { wk := add(wk, 1) } {
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk)))))
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // split the absorb: final_step, draw, extras). next_claim unused (sccl recomputes).
    next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, 25)
}

            function scl2_caches() {
            }
            function scl2_g0(alpha, a) -> acc { acc := a
    // CopyInExtensionField: [24] = 15
    acc := gate_copyinextensionfield(alpha, acc, 24)
    
    // CopyInExtensionField: [23] = 14
    acc := gate_copyinextensionfield(alpha, acc, 23)
    
    // CopyInExtensionField: [18] = 13
    acc := gate_copyinextensionfield(alpha, acc, 18)
    
    // CopyInExtensionField: [17] = 12
    acc := gate_copyinextensionfield(alpha, acc, 17)
    
    // AggregateLookupRationalPair: [21]/[22] + [19]/[20] = 10/11
    acc := gate_aggregatelookuprationalpair(alpha, acc, 21, 19, 22, 20)
    
    // CopyInExtensionField: [12] = 9
    acc := gate_copyinextensionfield(alpha, acc, 12)
    
    // CopyInExtensionField: [11] = 8
    acc := gate_copyinextensionfield(alpha, acc, 11)
    
    // AggregateLookupRationalPair: [15]/[16] + [13]/[14] = 6/7
    acc := gate_aggregatelookuprationalpair(alpha, acc, 15, 13, 16, 14)
    
    // AggregateLookupRationalPair: [5]/[6] + [3]/[4] = 4/5
    acc := gate_aggregatelookuprationalpair(alpha, acc, 5, 3, 6, 4)
    
    // AggregateLookupRationalPair: [9]/[10] + [7]/[8] = 2/3
    acc := gate_aggregatelookuprationalpair(alpha, acc, 9, 7, 10, 8)
    
    // MaskIntoIdentityProduct: [2]*[0] + (1-[0]) = 1
    acc := gate_maskintoidentityproduct(alpha, acc, 2, 0)
    
    // MaskIntoIdentityProduct: [1]*[0] + (1-[0]) = 0
    acc := gate_maskintoidentityproduct(alpha, acc, 1, 0)
    
            }
            function sccl2(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := 0
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 15))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 14))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 13))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 12))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 11))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 10))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 0))))
            }
function sumcheck_circuit_layer1(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl1(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc
            mstore(CIRCUIT_PTR, ptr)
            scl1_caches()
            acc := scl1_g0(alpha, acc)
            acc := scl1_g1(alpha, acc)
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }

    
            // WRITEBACK claims for next layer (72 evals)
                for { let wk := 0 } lt(wk, 72) { wk := add(wk, 1) } {
                    mstore(add(GKR_CIRCUIT_CLAIMS_PTR(), mul(32, wk)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, wk)))))
                }
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // split the absorb: final_step, draw, extras). next_claim unused (sccl recomputes).
    {
            let base := mload(CIRCUIT_PTR)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            let bp := add(GKR_ABS_PTR(), 32)
            calldatacopy(bp, add(base, mul(16, 0)), mul(16, 8)) bp := add(bp, mul(16, 8))
            calldatacopy(bp, add(base, mul(16, 48)), mul(16, 24)) bp := add(bp, mul(16, 24))
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4))))) bp := add(bp, 16)
            let s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR())) mstore(SEED_PTR(), s)
            s := keccak256(SEED_PTR(), 32) mstore(SEED_PTR(), s)
            next_alpha := mod(shr(128, s), P)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            bp := add(GKR_ABS_PTR(), 32)
            calldatacopy(bp, add(base, mul(16, 8)), mul(16, 40)) bp := add(bp, mul(16, 40))
            s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR())) mstore(SEED_PTR(), s)
            next_ptr := add(ptr, mul(16, 72))
            next_claim := 0
            }
}

            function scl1_caches() {
    {  // VectorizedLookup: (0 + 1[9]) + (0 + 1[10]) + (0 + 1[11]) + (0 + 0) + (0 + 0) + (0 + 0) + (0 + 0) + (0 + 0) + (0 + 0) + (0 + 1[8]) = Cache(0)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P))), add(0, 0)), add(0, 0)), add(0, 0)), add(0, 0)), add(0, 0)), add(0, 0)), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)), mod(gate, P))
    }
    {  // VectorizedLookup: (0 + 1[13]) + (0 + 1[14]) + (0 + 1[15]) + (0 + 1[16]) + (0 + 1[17]) + (0 + 1[18]) + (0 + 1[19]) + (0 + 1[20]) + (0 + 0) + (0 + 1[12]) = Cache(1)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 12)))), P))), add(0, 0)), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 15)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 14)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 13)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)), mod(gate, P))
    }
    {  // VectorizedLookup: (0 + 1[22]) + (0 + 1[23]) + (0 + 1[24]) + (0 + 1[25]) + (0 + 1[26]) + (0 + 1[27]) + (0 + 1[28]) + (0 + 1[29]) + (0 + 0) + (0 + 1[21]) = Cache(2)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P))), add(0, 0)), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 29)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)), mod(gate, P))
    }
    {  // VectorizedLookup: (0 + 1[31]) + (0 + 1[32]) + (0 + 1[33]) + (0 + 1[34]) + (0 + 1[35]) + (0 + 1[36]) + (0 + 1[37]) + (0 + 1[38]) + (0 + 0) + (0 + 1[30]) = Cache(3)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 30)))), P))), add(0, 0)), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 38)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 37)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 36)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 35)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 34)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 33)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 32)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 31)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)), mod(gate, P))
    }
    {  // VectorizedLookup: (0 + 1[40]) + (0 + 1[41]) + (0 + 1[42]) + (0 + 1[43]) + (0 + 1[44]) + (0 + 1[45]) + (0 + 1[46]) + (0 + 1[47]) + (0 + 0) + (0 + 1[39]) = Cache(4)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 39)))), P))), add(0, 0)), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)), mod(gate, P))
    }
            }
            function scl1_g0(alpha, a) -> acc { acc := a
    // CopyInExtensionField: [5] = 24
    acc := gate_copyinextensionfield(alpha, acc, 5)
    
    // CopyInExtensionField: [6] = 23
    acc := gate_copyinextensionfield(alpha, acc, 6)
    
    {  // LookupUnbalancedPairWithMaterializedVectorInputs: [70]/[71] + 1/(δ + Cache(4)) = 21/22
        let den_out := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedVectorInputs: 1/(δ+Cache(2)) + 1/(δ+Cache(3)) = 19/20
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedVectorInputs: 1/(δ+Cache(0)) + 1/(δ+Cache(1)) = 17/18
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    // CopyInExtensionField: [62] = 16
    acc := gate_copyinextensionfield(alpha, acc, 62)
    
    // CopyInExtensionField: [61] = 15
    acc := gate_copyinextensionfield(alpha, acc, 61)
    
    // AggregateLookupRationalPair: [65]/[66] + [63]/[64] = 13/14
    acc := gate_aggregatelookuprationalpair(alpha, acc, 65, 63, 66, 64)
    
    {  // LookupUnbalancedPairWithMaterializedBaseInputs: [67]/[68] + 1/(δ + [69]) = 11/12
        let den_out := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69))))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupUnbalancedPairWithMaterializedBaseInputs: [48]/[49] + 1/(δ + [7]) = 9/10
        let den_out := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7))))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    // AggregateLookupRationalPair: [52]/[53] + [50]/[51] = 7/8
    acc := gate_aggregatelookuprationalpair(alpha, acc, 52, 50, 53, 51)
    
    // AggregateLookupRationalPair: [56]/[57] + [54]/[55] = 5/6
    acc := gate_aggregatelookuprationalpair(alpha, acc, 56, 54, 57, 55)
    
            }
            function scl1_g1(alpha, a) -> acc { acc := a
    {  // LookupUnbalancedPairWithMaterializedBaseInputs: [58]/[59] + 1/(δ + [60]) = 3/4
        let den_out := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60))))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60))))), P), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // TrivialProduct: [2]*[4] = 2
        let gate := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 4)))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // TrivialProduct: [1]*[3] = 1
        let gate := mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 1)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInBaseField: [0] = 0
        let gate := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 0))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function sccl1(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := 0
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 24))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 23))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 22))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 21))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 20))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 19))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 18))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 17))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 16))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 15))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 14))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 13))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 12))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 11))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 10))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 0))))
            }
function sumcheck_circuit_layer0(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // INITIAL CLAIM: batch the previous layer's claims (heap array) in gate/slot order
    // (compute_claim). Replaces the threaded scalar; alpha == this layer's batching.
    claim := sccl0(alpha)
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc
            mstore(CIRCUIT_PTR, ptr)
            scl0_caches()
            acc := scl0_g0(alpha, acc)
            acc := scl0_g1(alpha, acc)
            acc := scl0_g2(alpha, acc)
            acc := scl0_g3(alpha, acc)
            acc := scl0_g4(alpha, acc)
            acc := scl0_g5(alpha, acc)
            acc := scl0_g6(alpha, acc)
            acc := scl0_g7(alpha, acc)
            acc := scl0_g8(alpha, acc)
            acc := scl0_g9(alpha, acc)
            acc := scl0_g10(alpha, acc)
            acc := scl0_g11(alpha, acc)
            acc := scl0_g12(alpha, acc)
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }

    
    // POINT CLAIMS BATCH — absorb this layer's evals + draw next_alpha (cache layers
    // split the absorb: final_step, draw, extras). next_claim unused (sccl recomputes).
    {
            let base := mload(CIRCUIT_PTR)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            let bp := add(GKR_ABS_PTR(), 32)
            calldatacopy(bp, add(base, mul(16, 38)), mul(16, 67)) bp := add(bp, mul(16, 67))
            calldatacopy(bp, add(base, mul(16, 2)), mul(16, 2)) bp := add(bp, mul(16, 2))
            calldatacopy(bp, add(base, mul(16, 5)), mul(16, 7)) bp := add(bp, mul(16, 7))
            calldatacopy(bp, add(base, mul(16, 14)), mul(16, 24)) bp := add(bp, mul(16, 24))
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 5))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 6))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 7))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 8))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 9))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 10))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 11))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 12))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 13))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 14))))) bp := add(bp, 16)
            mstore(bp, shl(128, mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 15))))) bp := add(bp, 16)
            let s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR())) mstore(SEED_PTR(), s)
            s := keccak256(SEED_PTR(), 32) mstore(SEED_PTR(), s)
            next_alpha := mod(shr(128, s), P)
            mstore(GKR_ABS_PTR(), mload(SEED_PTR()))
            bp := add(GKR_ABS_PTR(), 32)
            calldatacopy(bp, add(base, mul(16, 0)), mul(16, 2)) bp := add(bp, mul(16, 2))
            calldatacopy(bp, add(base, mul(16, 4)), mul(16, 1)) bp := add(bp, mul(16, 1))
            calldatacopy(bp, add(base, mul(16, 12)), mul(16, 2)) bp := add(bp, mul(16, 2))
            calldatacopy(bp, add(base, mul(16, 105)), mul(16, 10)) bp := add(bp, mul(16, 10))
            s := keccak256(GKR_ABS_PTR(), sub(bp, GKR_ABS_PTR())) mstore(SEED_PTR(), s)
            next_ptr := add(ptr, mul(16, 115))
            next_claim := 0
            }
}

            function scl0_caches() {
    {  // MemoryTuple: (γ + 0 + α[4] + α²0 + α³(0 + [0]) + α⁴[1] + α⁵[2] + α⁶[3]) = Cache(0)
        let gate := add(gkr_memrel_compress_low(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 4)))), 0), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 0))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 1)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + [9] + α[10] + α²[11] + α³(0 + [5]) + α⁴[6] + α⁵[7] + α⁶[8]) = Cache(1)
        let gate := add(gkr_memrel_compress_low(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11))))), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 5))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 6)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + 0 + α[4] + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[2] + α⁶[3]) = Cache(2)
        let gate := add(gkr_memrel_compress_low(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 4)))), 0), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + [9] + α[10] + α²[11] + α³(1 + [24]) + α⁴[25] + α⁵[7] + α⁶[8]) = Cache(3)
        let gate := add(gkr_memrel_compress_low(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11))))), gkr_memrel_compress_high(add(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + [16] + α[17] + α²[18] + α³(0 + [12]) + α⁴[13] + α⁵[14] + α⁶[15]) = Cache(4)
        let gate := add(gkr_memrel_compress_low(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18))))), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 12))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 13)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 14)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 15))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + 2 + α0 + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[22] + α⁶[23]) = Cache(5)
        let gate := add(gkr_memrel_compress_low(2, 0, 0), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 5)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + [16] + α[17] + α²[18] + α³(2 + [24]) + α⁴[25] + α⁵[19] + α⁶[20]) = Cache(6)
        let gate := add(gkr_memrel_compress_low(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18))))), gkr_memrel_compress_high(add(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 6)), mod(gate, P))
    }
    {  // MemoryTuple: (γ + 2 + α0 + α²0 + α³(0 + [28]) + α⁴[29] + α⁵[26] + α⁶[27]) = Cache(7)
        let gate := add(gkr_memrel_compress_low(2, 0, 0), gkr_memrel_compress_high(add(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 29)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27))))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 7)), mod(gate, P))
    }
    {  // SingleColumnLookup: 0 + -1[24] + 1[0] + 2^19[99] = Cache(8)
        let gate := add(0, add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 0)))), P)), mulmod(524288, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 99)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 8)), mod(gate, P))
    }
    {  // SingleColumnLookup: 2^19 + -1[25] + 1[1] + -1[99] = Cache(9)
        let gate := add(524288, add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 1)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 99)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 9)), mod(gate, P))
    }
    {  // SingleColumnLookup: -1 + -1[24] + 1[5] + 2^19[100] = Cache(10)
        let gate := add(sub(P, 1), add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 5)))), P)), mulmod(524288, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 100)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 10)), mod(gate, P))
    }
    {  // SingleColumnLookup: 2^19 + -1[25] + 1[6] + -1[100] = Cache(11)
        let gate := add(524288, add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 6)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 100)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 11)), mod(gate, P))
    }
    {  // SingleColumnLookup: -2 + -1[24] + 1[12] + 2^19[101] = Cache(12)
        let gate := add(sub(P, 2), add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 12)))), P)), mulmod(524288, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 101)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 12)), mod(gate, P))
    }
    {  // SingleColumnLookup: 2^19 + -1[25] + 1[13] + -1[101] = Cache(13)
        let gate := add(524288, add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 13)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 101)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 13)), mod(gate, P))
    }
    {  // VectorizedLookup: (0 + 1[22]) + (0 + 1[23]) + (0 + 1[4]) + (0 + 1[38]) + (0 + 1[39]) + (0 + 1[40]) + (0 + 1[41]) + (0 + 1[42]) + (0 + 1[43] + 2[44] + 2^2[45] + 2^3[46] + 2^4[47] + 2^5[48] + 2^6[49] + 2^7[50] + 2^8[51] + 2^9[52] + 2^10[53] + 2^11[54] + 2^12[55] + 2^13[56] + 2^14[57] + 2^15[58] + 2^16[59] + 2^17[60] + 2^18[9] + 2^19[16]) + (46 + 0) = Cache(14)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, add(46, 0)), add(0, add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), P), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), P)), mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), P)), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P)), mulmod(16, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P)), mulmod(32, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), P)), mulmod(64, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), P)), mulmod(128, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), P)), mulmod(512, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), P)), mulmod(1024, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P)), mulmod(2048, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(4096, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(8192, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(16384, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P)), mulmod(32768, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P)), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P)), mulmod(131072, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P)), mulmod(262144, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P)), mulmod(524288, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 39)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 38)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 4)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))), P))), add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), P)))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 14)), mod(gate, P))
    }
    {  // VectorizedLookupSetup: β⁰[105] + β¹[106] + β²[107] + β³[108] + β⁴[109] + β⁵[110] + β⁶[111] + β⁷[112] + β⁸[113] + β⁹[114] = Cache(15)
        let gate := gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(gkr_lookrel_step(0, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 114))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 113))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 112))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 111))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 110))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 109))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 108))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 107))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 106))))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 105)))))
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 15)), mod(gate, P))
    }
    {  // RangeCheck16Bits: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8])(1 - r[7])(1 - r[6])(1 - r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = Cache(16)
        let gate := gkr_virtual_poly_rangecheck(16)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)), mod(gate, P))
    }
    {  // RangeCheckTimestamp: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8] + 2^16 r[7] + 2^17 r[6] + 2^18 r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = Cache(17)
        let gate := gkr_virtual_poly_rangecheck(19)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)), mod(gate, P))
    }
    {  // InitsAndTeardownsLow: 4(2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10]) = Cache(18)
        let gate := mul(4, gkr_virtual_poly_compose_vars(14, 0)) // u32 word-aligned
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18)), mod(gate, P))
    }
    {  // InitsAndTeardownsHigh: 2^0 r[9] + 2^1 r[8] + 2^2 r[7] + 2^3 r[6] + 2^4 r[5] + 2^5 r[4] + 2^6 r[3] + 2^7 r[2] + 2^8 r[1] + 2^9 r[0] = Cache(19)
        let gate := gkr_virtual_poly_compose_vars(8, 14)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19)), mod(gate, P))
    }
            }
            function scl0_g0(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[101] + [101](1[101])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 101)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 101)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 101)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[100] + [100](1[100])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 100)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 100)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 100)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[99] + [99](1[99])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 99)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 99)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 99)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[98] + [98](1[98])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 98)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 98)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 98)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[97] + [97](1[97])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[96] + [96](1[96])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[95] + [95](1[95])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[94] + [94](1[94])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[93] + [93](1[93])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[92] + [92](1[92])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[65] + [65](1[65])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[64] + [64](1[64])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g1(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[63] + [63](1[63])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[62] + [62](1[62])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[61] + [61](1[61])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[16] + [16](1[16])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[9] + [9](1[9])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[60] + [60](1[60])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[59] + [59](1[59])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[58] + [58](1[58])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[57] + [57](1[57])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[56] + [56](1[56])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[55] + [55](1[55])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[54] + [54](1[54])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g2(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[53] + [53](1[53])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[52] + [52](1[52])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[51] + [51](1[51])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[50] + [50](1[50])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[49] + [49](1[49])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[48] + [48](1[48])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[47] + [47](1[47])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[46] + [46](1[46])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[45] + [45](1[45])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[44] + [44](1[44])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[43] + [43](1[43])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0x380000000000000000000000000 + 0xe0000000000000000000000000[24] + -1[25] + 0x6ffff20000000000000000000000001[28] + 1[29] + 0
        let gate := add(add(0x380000000000000000000000000, add(add(add(mulmod(0xe0000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 25)))), P)), mulmod(0x6ffff20000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 29)))), P))), 0)
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g3(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0x37ffe4000000000000000000000 + 0xdfff2000000000000000000000[24] + 0x6ffff2000e000000000000000000001[28] + [24](0x6ffffffffe400000000000000000001[24] + 0x3800000000000000000000[28]) + [28](0x6ffffffffe400000000000000000001[28])
        let gate := add(add(0x37ffe4000000000000000000000, add(mulmod(0xdfff2000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P), mulmod(0x6ffff2000e000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))), P))), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), add(mulmod(0x6ffffffffe400000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 24)))), P), mulmod(0x3800000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))), mulmod(0x6ffffffffe400000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[43] + 1[44] + 1[45] + 1[46] + 1[47] + 1[48] + 1[49] + 1[50] + 1[51] + 1[52] + 1[53] + 1[54] + 1[55] + 1[56] + 1[57] + 1[58] + 1[59] + 1[60] + 1[9] + 1[16] + [43](-1[21]) + [44](-1[21]) + [45](-1[21]) + [46](-1[21]) + [47](-1[21]) + [48](-1[21]) + [49](-1[21]) + [50](-1[21]) + [51](-1[21]) + [52](-1[21]) + [53](-1[21]) + [54](-1[21]) + [55](-1[21]) + [56](-1[21]) + [57](-1[21]) + [58](-1[21]) + [59](-1[21]) + [60](-1[21]) + [9](-1[21]) + [16](-1[21])
        let gate := add(add(0, add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P))), add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[98] + [43](-1[21]) + [44](-1[21]) + [45](-1[21]) + [46](-1[21]) + [47](-1[21]) + [48](-1[21]) + [49](-1[21]) + [50](-1[21]) + [51](-1[21]) + [52](-1[21]) + [53](-1[21]) + [54](-1[21]) + [55](-1[21]) + [56](-1[21]) + [58](-1[21]) + [59](-1[21]) + [60](-1[21]) + [9](-1[21]) + [16](-1[21])
        let gate := add(add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 98)))), P)), add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 51)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [96](1[97]) + [97](1[23] + -1[27])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 2^2[97] + [96](-2^16[97]) + [97](1[22] + -1[26])
        let gate := add(add(0, mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97)))), P)), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 96)))), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[97] + -1[21] + [53](1[21]) + [54](1[21]) + [55](1[21]) + [56](1[21])
        let gate := add(add(0, add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 97)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P))), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [64](1[9] + 1[16]) + [65](1[9] + 1[16])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [64](1[16]) + [65](2[16]) + [87](2^2[16]) + [16](-1[17])
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [64](1[9]) + [65](2[9]) + [87](2^2[9]) + [9](-1[10])
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[95] + [63](-1[9] + -1[16])
        let gate := add(add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [63](1[16])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [67](1[16]) + [16](-1[18])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g4(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [67](1[9]) + [9](-1[11])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [66](1[16]) + [16](-1[17])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [66](1[9]) + [9](-1[10])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [41](1[9] + 1[16]) + [61](1[9] + 1[16]) + [62](-2^16[9] + -2^16[16]) + [3](1[9] + 1[16]) + [9](-1[11]) + [16](-1[18])
        let gate := add(add(0, 0), add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [40](1[9] + 1[16]) + [61](-2^16[9] + -2^16[16]) + [2](1[9] + 1[16]) + [9](-1[10]) + [16](-1[17])
        let gate := add(add(0, 0), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[18] + [16](-1[18])
        let gate := add(add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[39] + 1[17] + [39](1[16]) + [16](-1[17])
        let gate := add(add(0, add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 39)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), P))), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 39)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[11] + [9](-1[11])
        let gate := add(add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[38] + 1[10] + [38](1[9]) + [9](-1[10])
        let gate := add(add(0, add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 38)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), P))), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 38)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [58](1[69] + 2^8[70] + 1[73] + 2^8[74] + 1[77] + 2^8[78] + 1[81] + 2^8[82] + -1[20]) + [59](1[69] + 2^8[70] + -1[20]) + [60](1[69] + 2^8[70] + 1[72] + 2^8[73] + 1[75] + 2^8[76] + 2^8[79] + 1[82] + -1[20])
        let gate := add(add(0, 0), add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(add(add(add(add(add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 73)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 74)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 77)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 78)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 81)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 82)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), add(add(add(add(add(add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 72)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 73)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 75)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 76)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 79)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 82)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [58](1[67] + 2^8[68] + 1[71] + 2^8[72] + 1[75] + 2^8[76] + 1[79] + 2^8[80] + -1[19]) + [59](1[67] + 2^8[68] + -1[19]) + [60](1[67] + 2^8[68] + 2^8[71] + 1[74] + 1[77] + 2^8[78] + 1[80] + 2^8[81] + -1[19])
        let gate := add(add(0, 0), add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(add(add(add(add(add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 72)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 75)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 76)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 79)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 80)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), add(add(add(add(add(add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 74)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 77)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 78)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 80)))), P)), mulmod(256, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 81)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[58] + -1[59] + -1[60] + [58](1[58] + 2[59] + 2[60]) + [59](1[59] + 2[60]) + [60](1[60])
        let gate := add(add(0, add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P))), add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g5(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [94](1[20])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [94](1[19])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [93](1[20])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [88](1[92]) + [92](-1[20])
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [68](1[93]) + [87](1[92]) + [92](-1[19]) + [93](-1[19])
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[94] + [53](-1[57]) + [54](-1[57]) + [55](-1[57]) + [56](-1[57])
        let gate := add(add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 94)))), P)), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[55] + 1[93] + [55](1[57])
        let gate := add(add(0, add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 93)))), P))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[53] + -1[54] + 1[92] + [53](1[57]) + [54](1[57])
        let gate := add(add(0, add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 92)))), P))), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 57)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [53](1[65]) + [54](1[65]) + [65](1[91])
        let gate := add(add(0, 0), add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [41](1[53] + 1[54] + 1[91]) + [53](1[63] + -2^16[64] + 1[23] + -1[27]) + [54](1[63] + -2^16[64] + 1[3] + -1[27]) + [55](1[63] + -2^16[64] + 1[23] + -1[27]) + [56](1[63] + -2^16[64] + 1[23] + -1[27])
        let gate := add(add(0, 0), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 2^2[55] + 2^2[56] + -2^2[91] + [40](1[53] + 1[54] + 1[91]) + [53](-2^16[63] + -1[90] + 1[22]) + [54](-2^16[63] + -1[90] + 1[2]) + [55](-2^16[63] + -1[90] + 1[22]) + [56](-2^16[63] + -1[90] + 1[22])
        let gate := add(add(0, add(add(mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P), mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(sub(P, 4), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))), P))), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[91] + [56](1[68])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 91)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g6(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [41](-1[55]) + [53](1[69] + -1[8]) + [54](1[69] + -1[8]) + [55](1[69] + -1[8]) + [56](1[69] + -1[8])
        let gate := add(add(0, 0), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [41](1[55]) + [53](1[61] + -2^16[62] + -1[88] + 1[23]) + [54](1[61] + -2^16[62] + -1[88] + 1[23]) + [55](1[61] + -2^16[62] + 1[88] + -1[3] + 1[8]) + [56](1[61] + -2^16[62] + 1[88] + -1[3] + 1[8])
        let gate := add(add(0, 0), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 2^2[53] + 2^2[54] + [40](1[55]) + [53](-2^16[61] + -1[87] + 1[22]) + [54](-2^16[61] + -1[87] + 1[22]) + [55](-2^16[61] + 1[87] + -1[2] + 1[7]) + [56](-2^16[61] + 1[87] + -1[2] + 1[7])
        let gate := add(add(0, add(mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P))), add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [50](1[20])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [50](1[19])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [50](1[6])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 6)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [50](1[5])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 5)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [50](1[8])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [50](1[7])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 50)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [52](-2^16[61] + 1[62] + 1[63] + -2^16[64] + 1[3] + 1[8] + 1[15] + -1[20])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), add(add(add(add(add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P)), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 64)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 15)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [52](-2^16[62] + -2^16[63] + 1[2] + 1[7] + 1[14] + -1[19])
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 52)))), add(add(add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 14)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 65535[46] + 65535[47] + 65535[48] + 65535[49] + [41](1[43] + 1[45]) + [43](-2^16[61] + 1[62] + 1[3] + 1[8] + -1[20]) + [44](-2^16[61] + 1[62] + -1[3] + 1[8] + 1[20]) + [45](-2^16[61] + 1[62] + -1[20] + 1[23]) + [46](-2^16[61] + 1[62] + 1[88] + -1[20]) + [47](-2^16[61] + 1[62] + 1[88] + -1[20]) + [48](-2^16[61] + 1[62] + 1[88] + -1[20]) + [49](-2^16[61] + 1[62] + 1[88] + -1[20])
        let gate := add(add(0, add(add(add(mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P), mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P)), mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), P)), mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), P))), add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), add(add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), add(add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g7(alpha, a) -> acc { acc := a
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 65535[46] + 65535[47] + 65535[48] + 65535[49] + [40](1[43] + 1[45]) + [43](-2^16[62] + 1[2] + 1[7] + -1[19]) + [44](-2^16[62] + -1[2] + 1[7] + 1[19]) + [45](-2^16[62] + -1[19] + 1[22]) + [46](-2^16[62] + 1[87] + -1[19]) + [47](-2^16[62] + 1[87] + -1[19]) + [48](-2^16[62] + 1[87] + -1[19]) + [49](-2^16[62] + 1[87] + -1[19])
        let gate := add(add(0, add(add(add(mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P), mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P)), mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), P)), mulmod(65535, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), P))), add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 43)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 44)))), add(add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 45)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 22)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), add(add(mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[46] + 1[47] + 1[48] + 1[49] + [46](-1[61]) + [47](-1[61]) + [48](-1[61]) + [49](-1[61])
        let gate := add(add(0, add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), P))), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 61)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + [46](-1[2] + -2^16[3] + -1[7] + -2^16[8] + 1[19] + 2^16[20]) + [47](-1[2] + -2^16[3] + 1[7] + 2^16[8] + 1[19] + 2^16[20]) + [48](-1[89] + 1[19] + 2^16[20]) + [49](-1[89] + 1[19] + 2^16[20])
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 46)))), add(add(add(add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 47)))), add(add(add(add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P), mulmod(sub(P, 65536), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 48)))), add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 89)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 49)))), add(add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 89)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[21] + [21](1[21])
        let gate := add(add(0, mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupWithCachedDensAndSetup: (([21])·((Cache(15))+δ) − ([104])·((Cache(14))+δ)) / (((Cache(14))+δ)((Cache(15))+δ)) = 70/71
        let bg := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 14))))
        let dg := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 15))))
        let den_out := mulmod(bg, dg, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), dg, P), sub(mul(2, P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 104)))), bg, P)))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInBaseField: Cache(13) = 69
        let gate := mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 13)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+Cache(11)) + 1/(δ+Cache(12)) = 67/68
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 11))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 12))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+Cache(9)) + 1/(δ+Cache(10)) = 65/66
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 9))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 10))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[29]) + 1/(δ+Cache(8)) = 63/64
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 29)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 8))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupFromMaterializedBaseInputWithSetup: 1/(δ + [28]) - [103]/(δ + Cache(17)) = 61/62
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28))))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 17)))), sub(P, mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 103)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 28))))), P)))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInBaseField: [27] = 60
        let gate := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 27))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[18]) + 1/(δ+[26]) = 58/59
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 18)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g8(alpha, a) -> acc { acc := a
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[11]) + 1/(δ+[17]) = 56/57
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 11)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 17)))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[90]) + 1/(δ+[10]) = 54/55
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 10)))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[20]) + 1/(δ+[23]) = 52/53
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 23)))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupPairFromMaterializedBaseInputs: 1/(δ+[88]) + 1/(δ+[19]) = 50/51
        let den1 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))))
        let den2 := add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))))
        let den_out := mulmod(den1, den2, P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(den1, den2)
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // LookupFromMaterializedBaseInputWithSetup: 1/(δ + [87]) - [102]/(δ + Cache(16)) = 48/49
        let den_out := mulmod(add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87))))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)))), P)
        let gate := den_out
        acc := add(mulmod(acc, alpha, P), gate)
        let num_out := add(add(mload(add(LOGUP_CHALLS_PTR(), 32)), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 16)))), sub(P, mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 102)))), add(mload(add(LOGUP_CHALLS_PTR(), 32)), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87))))), P)))
        gate := num_out
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[82]) = 47
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 82)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[81]) = 46
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 81)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[80]) + [60](1[82]) = 45
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 80)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 82)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[79]) + [60](1[81]) = 44
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 79)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 81)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [42](1[58]) + [60](1[80]) = 43
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 80)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [40](1[58]) + [53](1[26]) + [54](1[26]) + [55](1[26]) + [56](1[26]) + [58](1[66]) + [59](1[70]) + [60](1[79]) = 42
        let gate := add(add(0, 0), add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 26)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 79)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [53](1[65]) + [54](1[65]) + [55](1[65]) + [56](1[65]) + [58](0x70000000000000000000000000000[84] + 0x6f90000000000000000000000000001[3]) + [59](1[66] + 0x70000000000000000000000000000[86] + 0x6f90000000000000000000000000001[8]) + [60](0x70000000000000000000000000000[86] + 0x6f90000000000000000000000000001[8]) = 41
        let gate := add(add(0, 0), add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 65)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 84)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86)))), P)), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g9(alpha, a) -> acc { acc := a
    {  // MaxQuadratic: 0 + 3[58] + [53](1[90]) + [54](1[90]) + [55](1[90]) + [56](1[90]) + [59](0x70000000000000000000000000000[84] + 0x6f90000000000000000000000000001[3]) + [60](0x70000000000000000000000000000[84] + 0x6f90000000000000000000000000001[3]) = 40
        let gate := add(add(0, mulmod(3, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P)), add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 90)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 84)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 84)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 2[53] + 2[54] + 2[55] + 2[56] + 9[58] + [42](1[59] + 1[60]) = 39
        let gate := add(add(0, add(add(add(add(mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(9, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P)), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[78]) = 38
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 78)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[77]) = 37
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 77)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[76]) + [60](1[78]) = 36
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 76)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 78)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[75]) + [60](1[77]) = 35
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 75)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 77)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [42](1[58]) + [60](1[76]) = 34
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 76)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [40](1[58]) + [58](1[66]) + [59](1[69]) + [60](1[75]) = 33
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 75)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [53](1[68]) + [54](1[68]) + [55](1[68]) + [56](1[68]) + [58](1[84]) + [59](1[66] + 1[86]) + [60](1[86]) = 32
        let gate := add(add(0, 0), add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 84)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 86)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 2[58] + [42](2^4[53] + 2^4[54] + 2^4[55] + 2^4[56]) + [53](2^2[62] + 2^3[66] + 2[67] + 1[70]) + [54](2^2[62] + 2^3[66] + 2[67] + 1[70]) + [55](2^2[62] + 2^3[66] + 2[67] + 1[70]) + [56](2^2[62] + 2^3[66] + 2[67] + 1[70]) + [59](1[84]) + [60](1[84]) = 31
        let gate := add(add(0, mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P)), add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), add(add(add(mulmod(16, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(16, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(16, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(16, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(add(add(mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(add(add(mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(add(add(mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(add(add(mulmod(4, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 62)))), P), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P)), mulmod(2, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 84)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 84)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 51[53] + 51[54] + 51[55] + 51[56] + 9[58] + [42](1[59] + 1[60]) = 30
        let gate := add(add(0, add(add(add(add(mulmod(51, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(51, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(51, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(51, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(9, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P)), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[74]) = 29
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 74)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g10(alpha, a) -> acc { acc := a
    {  // MaxQuadratic: 0 + 0 + [58](1[73]) = 28
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 73)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[72]) + [60](1[74]) = 27
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 72)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 74)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[71]) + [60](1[73]) = 26
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 73)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [42](1[58]) + [60](1[72]) = 25
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 72)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [40](1[58]) + [58](1[66]) + [59](1[68]) + [60](1[71]) = 24
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 71)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [41](1[59]) + [53](1[70]) + [54](1[70]) + [55](1[70]) + [56](1[70]) + [58](0x70000000000000000000000000000[83] + 0x6f90000000000000000000000000001[2]) + [59](0x70000000000000000000000000000[85] + 0x6f90000000000000000000000000001[7]) + [60](0x70000000000000000000000000000[85] + 0x6f90000000000000000000000000001[7]) = 23
        let gate := add(add(0, 0), add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 83)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 85)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 85)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 1[58] + [53](1[69]) + [54](1[69]) + [55](1[69]) + [56](1[69]) + [59](0x70000000000000000000000000000[83] + 0x6f90000000000000000000000000001[2]) + [60](0x70000000000000000000000000000[83] + 0x6f90000000000000000000000000001[2]) = 22
        let gate := add(add(0, mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P)), add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 83)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 83)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 2)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 5[53] + 5[54] + 5[55] + 5[56] + 9[58] + [42](1[59] + 1[60]) = 21
        let gate := add(add(0, add(add(add(add(mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(9, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P)), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[70]) = 20
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[69]) = 19
        let gate := add(add(0, 0), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[68]) + [60](1[70]) = 18
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 70)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[67]) + [60](1[69]) = 17
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 69)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g11(alpha, a) -> acc { acc := a
    {  // MaxQuadratic: 0 + 0 + [42](1[58]) + [60](1[68]) = 16
        let gate := add(add(0, 0), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 68)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [40](1[58]) + [58](1[66]) + [59](1[67]) + [60](1[67]) = 15
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [40](1[59]) + [53](1[67]) + [54](1[67]) + [55](1[67]) + [56](1[67]) + [58](1[83]) + [59](1[85]) + [60](1[85]) = 14
        let gate := add(add(0, 0), add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 40)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 83)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 85)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 85)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [53](1[3]) + [54](1[3]) + [55](1[3]) + [56](1[3]) + [59](1[83]) + [60](1[83]) = 13
        let gate := add(add(0, 0), add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 3)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 83)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 83)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 5[53] + 5[54] + 5[55] + 5[56] + 9[58] + [42](1[59] + 1[60]) = 12
        let gate := add(add(0, add(add(add(add(mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(5, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(9, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 42)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 60)))), P)), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [58](1[66]) + [8](1[95]) + [9](-1[8] + 1[20]) + [16](-1[8] + 1[20]) = 11
        let gate := add(add(0, 0), add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 8)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 20)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [53](1[66]) + [54](1[66]) + [55](1[66]) + [56](1[66]) + [58](0x70000000000000000000000000000[85] + 0x6f90000000000000000000000000001[7]) + [59](1[66]) + [7](1[95]) + [9](-1[7] + 1[19]) + [16](-1[7] + 1[19]) = 10
        let gate := add(add(0, 0), add(add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), add(mulmod(0x70000000000000000000000000000, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 85)))), P), mulmod(0x6f90000000000000000000000000001, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), add(mulmod(sub(P, 1), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 7)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 19)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 0 + [41](1[59]) + [53](1[87] + 1[88]) + [54](1[87] + 1[88]) + [55](1[87] + 1[88]) + [56](1[87] + 1[88]) + [58](1[85]) + [66](1[95]) + [67](2^16[95]) = 9
        let gate := add(add(0, 0), add(add(add(add(add(add(add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 41)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 87)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 88)))), P)), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 85)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 66)))), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), P), P)), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), P), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + 1[53] + 1[54] + 1[55] + 1[56] + 2^3[58] + 3[59] + [21](34[95]) = 8
        let gate := add(add(0, add(add(add(add(add(mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 53)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 54)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 55)))), P)), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 56)))), P)), mulmod(8, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 58)))), P)), mulmod(3, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 59)))), P))), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21)))), mulmod(34, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 95)))), P), P))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // MaxQuadratic: 0 + -2^6[9] + -2^6[16] + [9](2^16[63] + 1[67]) + [16](2^16[63] + 1[67]) = 7
        let gate := add(add(0, add(mulmod(sub(P, 64), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), P), mulmod(sub(P, 64), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), P))), add(mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 9)))), add(mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P)), P), mulmod(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 16)))), add(mulmod(65536, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 63)))), P), mulmod(1, shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 67)))), P)), P)))
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(18) + α²(Cache(19) + 0) + α³[32] + α⁴[33] + α⁵[30] + α⁶[31]) * (γ + 1 + αCache(18) + α²(Cache(19) + 256) + α³[36] + α⁴[37] + α⁵[34] + α⁶[35]) = 6
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR(), mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))), P))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), 0), P), gkr_memrel_compress_high(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 32)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 33)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 30)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 31))))))) // for memrel we collect
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), 256), P), gkr_memrel_compress_high(shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 36)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 37)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 34)))), shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 35))))))) // for memrel we collect
        let gate := mulmod(lhs, rhs, P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitsOrTeardownsInitialPair: (γ + 1 + αCache(18) + α²(Cache(19) + 0) + 0) * (γ + 1 + αCache(18) + α²(Cache(19) + 256) + 0) = 5
        let shared := add(add(mload(add(MEMORY_CHALLS_PTR(), mul(32, 6))), 1), mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 18))), P))
        let lhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), 0), P), 0)) // for memrel we collect
        let rhs := add(shared, add(mulmod(mload(add(MEMORY_CHALLS_PTR(), mul(32, 1))), add(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 19))), 256), P), 0)) // for memrel we collect
        let gate := mulmod(lhs, rhs, P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function scl0_g12(alpha, a) -> acc { acc := a
    {  // InitialGrandProductFromCaches: Cache(6)*Cache(7) = 4
        let gate := mulmod(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 6))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 7))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductFromCaches: Cache(4)*Cache(5) = 3
        let gate := mulmod(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 4))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 5))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductFromCaches: Cache(2)*Cache(3) = 2
        let gate := mulmod(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // InitialGrandProductFromCaches: Cache(0)*Cache(1) = 1
        let gate := mulmod(mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0))), mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1))), P)
        acc := add(mulmod(acc, alpha, P), gate)
    }
    {  // CopyInBaseField: [21] = 0
        let gate := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, 21))))
        acc := add(mulmod(acc, alpha, P), gate)
    }
            }
            function sccl0(alpha) -> claim {
            let src := GKR_CIRCUIT_CLAIMS_PTR()
            claim := 0
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := mulmod(claim, alpha, P)
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 71))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 70))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 69))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 68))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 67))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 66))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 65))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 64))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 63))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 62))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 61))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 60))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 59))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 58))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 57))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 56))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 55))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 54))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 53))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 52))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 51))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 50))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 49))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 48))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 47))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 46))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 45))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 44))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 43))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 42))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 41))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 40))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 39))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 38))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 37))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 36))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 35))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 34))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 33))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 32))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 31))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 30))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 29))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 28))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 27))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 26))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 25))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 24))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 23))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 22))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 21))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 20))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 19))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 18))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 17))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 16))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 15))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 14))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 13))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 12))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 11))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 10))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 9))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 8))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 7))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 6))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 5))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 4))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 3))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 2))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 1))))
            claim := add(mulmod(claim, alpha, P), mload(add(src, mul(32, 0))))
            }
function sumcheck_rounds_circuit(ptr, claim) -> next_ptr, next_claim, eq_scale {
    // NB: need to inline GKR_CIRCUIT_LAYER_ROUNDS unfortunately
    eq_scale := 1
    for { let i := 0 } lt(i, GKR_CIRCUIT_LAYER_ROUNDS) { i := add(i, 1) } {
        let w0 := calldataload(ptr)
        let w1 := calldataload(add(ptr, 32))
        let c0 := shr(128, w0)
        let c1 := and(w0, MASK)
        let c2 := shr(128, w1)
        let c3 := and(w1, MASK)
        let g0g1_scaled := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P)
        let r := transcript_4to1_dual(w0, w1) // before-check draw is intentional; see HEURISTICS.md
        // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
        if mod(add(claim, sub(P, g0g1_scaled)), P) { revert(0, 0) }
        if mod(add(claim, sub(P, g0g1_scaled)), P) { revert(0, 0) }

        claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
        let z := mload(add(POINT_PTR(), mul(i, 32)))
        let zr := mulmod(z, r, P)
        eq_scale := add(add(add(zr, zr), 1), sub(mul(4, P), add(z, r)))
        mstore(add(POINT_PTR(), mul(i, 32)), r)
        ptr := add(ptr, 64)
    }
    next_ptr := ptr
    next_claim := claim
}
function transcriptNto1(ptr, input_elements) -> alpha {
    let input_bytes := mul(input_elements, 16)
    calldatacopy(add(SEED_PTR(), 32), ptr, input_bytes)
    let seed := keccak256(SEED_PTR(), add(32, input_bytes)) // absorb evals
    mstore(SEED_PTR(), seed)
    seed := keccak256(SEED_PTR(), 32)                       // draw (the mirror draws a fresh el)
    mstore(SEED_PTR(), seed)
    alpha := mod(shr(128, seed), P)                         // batching is a field element mod P
}
function sumcheck_claims_batch(ptr, points) -> next_ptr, next_claim, next_alpha {
    let is_odd := mod(points, 2)
    if is_odd {
        next_claim := shr(128, calldataload(add(ptr, mul(16, sub(points, 1)))))
    }
    next_alpha := transcriptNto1(ptr, points)
    let even_points := sub(points, is_odd)
    let pairs := shr(1, even_points)
    for { let pair := sub(pairs, 1) } lt(pair, pairs) { pair := sub(pair, 1) } {
        let word := calldataload(add(ptr, mul(pair, 32)))
        let el1 := and(MASK, word)
        let el0 := shr(128, word)
        next_claim := add(mulmod(next_claim, next_alpha, P), el1)
        next_claim := add(mulmod(next_claim, next_alpha, P), el0)
    }
    next_ptr := add(ptr, mul(16, points))
}

function gkr_memrel_compress(address_space, addr_low, addr_high, ts_low, ts_high, val_low, val_high) -> compressed {
    compressed := add(mload(add(MEMORY_CHALLS_PTR(), 192)), address_space)
    compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR()), addr_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 32)), addr_high, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 64)), ts_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 96)), ts_high, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 128)), val_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 160)), val_high, P))
}

// Fold five generic lookup tuple columns into an existing Horner accumulator.
// A single helper that took all c0..c9 made solc materialize all ten columns
// at the call boundary and failed stack allocation. Splitting the fold into
// two five-column calls keeps each call boundary small while still supporting
// arbitrary linrel_to_calldata_inner() output for every column.
function gkr_lookrel_compress_half(acc, c0, c1, c2, c3, c4) -> acc_next {
    acc_next := add(mulmod(acc, mload(LOGUP_CHALLS_PTR()), P), c4)
    acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c3)
    acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c2)
    acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c1)
    acc_next := add(mulmod(acc_next, mload(LOGUP_CHALLS_PTR()), P), c0)
}
// One β-Horner step: acc·β + c. Callers chain ten of these (see lookrel_horner)
// instead of one 5-arg compress_half, keeping every call boundary at 2 args so the
// enclosing cache/gate function stays inside the EVM stack limit.
function gkr_lookrel_step(acc, c) -> acc_next {
    acc_next := add(mulmod(acc, mload(LOGUP_CHALLS_PTR()), P), c)
}

// Split memrel into a 3-arg low + 4-arg high, composed by the caller as
// add(low(...), high(...)). A single 7-arg gkr_memrel_compress forced solc to
// materialize all 7 expression-args at the call boundary, running the enclosing
// cache function 1 slot too deep (same failure the lookrel split above avoids).
function gkr_memrel_compress_low(address_space, addr_low, addr_high) -> compressed {
    compressed := add(mload(add(MEMORY_CHALLS_PTR(), 192)), address_space)
    compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR()), addr_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 32)), addr_high, P))
}
function gkr_memrel_compress_high(ts_low, ts_high, val_low, val_high) -> compressed {
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 64)), ts_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 96)), ts_high, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 128)), val_low, P))
    compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 160)), val_high, P))
}

function gkr_virtual_poly_compose_vars(len, skip) -> eval {
    // let total := add(skip, len)
    let max := sub(GKR_CIRCUIT_LAYER_ROUNDS, skip) // exclusive
    let min := sub(max, len)
    // NO NEED FOR THIS CHECK, WE DO IT VIA RUST
    // if gt(total, GKR_CIRCUIT_LAYER_ROUNDS) { // abort when bad
    //     min := max
    // }
    for { let i := min } lt(i, max) { i := add(i, 1) } {
        eval := add(mul(eval, 2), mload(add(POINT_PTR(), mul(i, 32))))
    }
}
function gkr_virtual_poly_zero_vars(len) -> eval {
    eval := 1
    for { let i := 0 } lt(i, len) { i := add(i, 1) } {
        eval := mulmod(eval, add(1, sub(mul(2, P), mload(add(POINT_PTR(), mul(i, 32))))), P)
    }
}
function gkr_virtual_poly_rangecheck(width) -> eval {
    eval := mulmod(gkr_virtual_poly_compose_vars(width, 0), gkr_virtual_poly_zero_vars(sub(GKR_CIRCUIT_LAYER_ROUNDS, width)), P)
}

function gate_calldataload(idx) -> load {
    load := shr(128, calldataload(add(mload(CIRCUIT_PTR), mul(16, idx))))
}
function gate_mload(idx) -> load {
    load := mload(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, idx)))
}
function pointcheck_update(acc, alpha, gate) -> next_acc {
    next_acc := add(mulmod(acc, alpha, P), gate)
}
function logup_pointcheck_update(acc, alpha, num_out, den_out) -> next_acc {
    acc := pointcheck_update(acc, alpha, den_out)
    next_acc := pointcheck_update(acc, alpha, num_out)
}
function u128_neg(input) -> neg_input {
    neg_input := sub(mul(2, P), input)
}

// 3
function gate_aggregatelookuprationalpair(alpha, acc, num1_idx, num2_idx, den1_idx, den2_idx) -> next_acc {
    let num1 := gate_calldataload(num1_idx)
    let num2 := gate_calldataload(num2_idx)
    let den1 := gate_calldataload(den1_idx)
    let den2 := gate_calldataload(den2_idx)
    let den_out := mulmod(den1, den2, P)
    let num_out := add(mulmod(num1, den2, P), mulmod(num2, den1, P))
    next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
}
function gate_copyinextensionfield(alpha, acc, input_idx) -> next_acc {
    let input := gate_calldataload(input_idx)
    next_acc := pointcheck_update(acc, alpha, input)
}

// 2
function gate_maskintoidentityproduct(alpha, acc, input_idx, mask_idx) -> next_acc {
    let input := gate_calldataload(input_idx)
    let mask := gate_calldataload(mask_idx)
    // let neg_mask := u128_neg(mask)
    // let gate := add(mulmod(input, mask, P), add(1, neg_mask))
    let neg_one := sub(P, 1)
    let gate := add(mulmod(mask, add(input, neg_one), P), 1)
    next_acc := pointcheck_update(acc, alpha, gate)
}

