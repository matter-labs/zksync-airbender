function sumcheck_circuit_layer3(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc
    // CopyInExtensionField: [15] = [9]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 15)
    
    // CopyInExtensionField: [14] = [8]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 14)
    
    // CopyInExtensionField: [1] = [7]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 1)
    
    // CopyInExtensionField: [0] = [6]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 0)
    
    // AggregateLookupRationalPair: [12]/[13] + [10]/[11] = [4]/[5]
    acc := gate_aggregatelookuprationalpair(ptr, alpha, acc, 12, 10, 13, 11)
    
    // AggregateLookupRationalPair: [8]/[9] + [6]/[7] = [2]/[3]
    acc := gate_aggregatelookuprationalpair(ptr, alpha, acc, 8, 6, 9, 7)
    
    // AggregateLookupRationalPair: [4]/[5] + [2]/[3] = [0]/[1]
    acc := gate_aggregatelookuprationalpair(ptr, alpha, acc, 4, 2, 5, 3)
    
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }


    // POINT CLAIMS BATCH (16 POINTS)
    next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, 16)
}

function sumcheck_circuit_layer2(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc
    // CopyInExtensionField: [24] = [15]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 24)
    
    // CopyInExtensionField: [23] = [14]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 23)
    
    // CopyInExtensionField: [18] = [13]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 18)
    
    // CopyInExtensionField: [17] = [12]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 17)
    
    // AggregateLookupRationalPair: [21]/[22] + [19]/[20] = [10]/[11]
    acc := gate_aggregatelookuprationalpair(ptr, alpha, acc, 21, 19, 22, 20)
    
    // CopyInExtensionField: [12] = [9]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 12)
    
    // CopyInExtensionField: [11] = [8]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 11)
    
    // AggregateLookupRationalPair: [15]/[16] + [13]/[14] = [6]/[7]
    acc := gate_aggregatelookuprationalpair(ptr, alpha, acc, 15, 13, 16, 14)
    
    // AggregateLookupRationalPair: [5]/[6] + [3]/[4] = [4]/[5]
    acc := gate_aggregatelookuprationalpair(ptr, alpha, acc, 5, 3, 6, 4)
    
    // AggregateLookupRationalPair: [9]/[10] + [7]/[8] = [2]/[3]
    acc := gate_aggregatelookuprationalpair(ptr, alpha, acc, 9, 7, 10, 8)
    
    // MaskIntoIdentityProduct: [2]*[0] + (1-[0]) = [1]
    acc := gate_maskintoidentityproduct(ptr, alpha, acc, 2, 0)
    
    // MaskIntoIdentityProduct: [1]*[0] + (1-[0]) = [0]
    acc := gate_maskintoidentityproduct(ptr, alpha, acc, 1, 0)
    
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }


    // POINT CLAIMS BATCH (25 POINTS)
    next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, 25)
}

function sumcheck_circuit_layer1(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc
    // CopyInExtensionField: [5] = [24]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 5)
    
    // CopyInExtensionField: [6] = [23]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 6)
    
    // LookupUnbalancedPairWithVectorInputs: [70]/[71] + 1/(δ + β⁰(0 + 1[40] + 0 + 0) + β¹(0 + 1[41] + 0 + 0) + β²(0 + 1[42] + 0 + 0) + β³(0 + 1[43] + 0 + 0) + β⁴(0 + 1[44] + 0 + 0) + β⁵(0 + 1[45] + 0 + 0) + β⁶(0 + 1[46] + 0 + 0) + β⁷(0 + 1[47] + 0 + 0) + β⁸(0 + 0 + 0 + 0) + β⁹(0 + 1[39] + 0 + 0)) = [21]/[22]
    acc := gate_lookupunbalancedpairwithvectorinputs(ptr, alpha, acc, 70, 71, 0)
    
    // LookupPairFromVectorInputs: 1/(δ + β⁰(0 + 1[22] + 0 + 0) + β¹(0 + 1[23] + 0 + 0) + β²(0 + 1[24] + 0 + 0) + β³(0 + 1[25] + 0 + 0) + β⁴(0 + 1[26] + 0 + 0) + β⁵(0 + 1[27] + 0 + 0) + β⁶(0 + 1[28] + 0 + 0) + β⁷(0 + 1[29] + 0 + 0) + β⁸(0 + 0 + 0 + 0) + β⁹(0 + 1[21] + 0 + 0)) + 1/(δ + β⁰(0 + 1[31] + 0 + 0) + β¹(0 + 1[32] + 0 + 0) + β²(0 + 1[33] + 0 + 0) + β³(0 + 1[34] + 0 + 0) + β⁴(0 + 1[35] + 0 + 0) + β⁵(0 + 1[36] + 0 + 0) + β⁶(0 + 1[37] + 0 + 0) + β⁷(0 + 1[38] + 0 + 0) + β⁸(0 + 0 + 0 + 0) + β⁹(0 + 1[30] + 0 + 0)) = [19]/[20]
    acc := gate_lookuppairfromvectorinputs(ptr, alpha, acc, 1, 2)
    
    // LookupPairFromVectorInputs: 1/(δ + β⁰(0 + 1[9] + 0 + 0) + β¹(0 + 1[10] + 0 + 0) + β²(0 + 1[11] + 0 + 0) + β³(0 + 0 + 0 + 0) + β⁴(0 + 0 + 0 + 0) + β⁵(0 + 0 + 0 + 0) + β⁶(0 + 0 + 0 + 0) + β⁷(0 + 0 + 0 + 0) + β⁸(0 + 0 + 0 + 0) + β⁹(0 + 1[8] + 0 + 0)) + 1/(δ + β⁰(0 + 1[13] + 0 + 0) + β¹(0 + 1[14] + 0 + 0) + β²(0 + 1[15] + 0 + 0) + β³(0 + 1[16] + 0 + 0) + β⁴(0 + 1[17] + 0 + 0) + β⁵(0 + 1[18] + 0 + 0) + β⁶(0 + 1[19] + 0 + 0) + β⁷(0 + 1[20] + 0 + 0) + β⁸(0 + 0 + 0 + 0) + β⁹(0 + 1[12] + 0 + 0)) = [17]/[18]
    acc := gate_lookuppairfromvectorinputs(ptr, alpha, acc, 3, 4)
    
    // CopyInExtensionField: [62] = [16]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 62)
    
    // CopyInExtensionField: [61] = [15]
    acc := gate_copyinextensionfield(ptr, alpha, acc, 61)
    
    // AggregateLookupRationalPair: [65]/[66] + [63]/[64] = [13]/[14]
    acc := gate_aggregatelookuprationalpair(ptr, alpha, acc, 65, 63, 66, 64)
    
    // LookupUnbalancedPairWithMaterializedBaseInputs: [67]/[68] + 1/(δ + [69]) = [11]/[12]
    acc := gate_lookupunbalancedpairwithmaterializedbaseinputs(ptr, alpha, acc, 67, 68, 69)
    
    // LookupUnbalancedPairWithMaterializedBaseInputs: [48]/[49] + 1/(δ + [7]) = [9]/[10]
    acc := gate_lookupunbalancedpairwithmaterializedbaseinputs(ptr, alpha, acc, 48, 49, 7)
    
    // AggregateLookupRationalPair: [52]/[53] + [50]/[51] = [7]/[8]
    acc := gate_aggregatelookuprationalpair(ptr, alpha, acc, 52, 50, 53, 51)
    
    // AggregateLookupRationalPair: [56]/[57] + [54]/[55] = [5]/[6]
    acc := gate_aggregatelookuprationalpair(ptr, alpha, acc, 56, 54, 57, 55)
    
    // LookupUnbalancedPairWithMaterializedBaseInputs: [58]/[59] + 1/(δ + [60]) = [3]/[4]
    acc := gate_lookupunbalancedpairwithmaterializedbaseinputs(ptr, alpha, acc, 58, 59, 60)
    
    // TrivialProduct: [2]*[4] = [2]
    acc := gate_trivialproduct(ptr, alpha, acc, 2, 4)
    
    // TrivialProduct: [1]*[3] = [1]
    acc := gate_trivialproduct(ptr, alpha, acc, 1, 3)
    
    // CopyInBaseField: [0] = [0]
    acc := gate_copyinbasefield(ptr, alpha, acc, 0)
    
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }


    // POINT CLAIMS BATCH (72 POINTS)
    next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, 72)
}

function sumcheck_circuit_layer0(ptr, claim, alpha) -> next_ptr, next_claim, next_alpha {
    // SUMCHECK ROUNDS
    let eq_scale
    // ptr, claim, eq_scale := sumcheck_rounds(ptr, claim, GKR_CIRCUIT_LAYER_ROUNDS) // BREAKS UNSAFE SOLX, BUT MUCH CHEAPER SOLX
    ptr, claim, eq_scale := sumcheck_rounds_circuit(ptr, claim)
    
    // POINT CHECK
    let acc
    {  // RangeCheck16Bits: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8])(1 - r[7])(1 - r[6])(1 - r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = Cache(0)
        let gate := gkr_virtual_poly_rangecheck(16)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 0)), mod(gate, P))
    }
    {  // RangeCheckTimestamp: (2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10] + 2^14 r[9] + 2^15 r[8] + 2^16 r[7] + 2^17 r[6] + 2^18 r[5])(1 - r[4])(1 - r[3])(1 - r[2])(1 - r[1])(1 - r[0]) = Cache(1)
        let gate := gkr_virtual_poly_rangecheck(19)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 1)), mod(gate, P))
    }
    {  // InitsAndTeardownsLow: 4(2^0 r[23] + 2^1 r[22] + 2^2 r[21] + 2^3 r[20] + 2^4 r[19] + 2^5 r[18] + 2^6 r[17] + 2^7 r[16] + 2^8 r[15] + 2^9 r[14] + 2^10 r[13] + 2^11 r[12] + 2^12 r[11] + 2^13 r[10]) = Cache(2)
        let gate := mul(4, gkr_virtual_poly_compose_vars(14, 0)) // u32 word-aligned
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 2)), mod(gate, P))
    }
    {  // InitsAndTeardownsHigh: 2^0 r[9] + 2^1 r[8] + 2^2 r[7] + 2^3 r[6] + 2^4 r[5] + 2^5 r[4] + 2^6 r[3] + 2^7 r[2] + 2^8 r[1] + 2^9 r[0] = Cache(3)
        let gate := gkr_virtual_poly_compose_vars(10, 14)
        mstore(add(GKR_CIRCUIT_CACHE_PTR(), mul(32, 3)), mod(gate, P))
    }
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[99] + 0 + 0 + [99](1[99] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 5)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[98] + 0 + 0 + [98](1[98] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 6)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[97] + 0 + 0 + [97](1[97] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 7)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[96] + 0 + 0 + [96](1[96] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 8)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[95] + 0 + 0 + [95](1[95] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 9)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[94] + 0 + 0 + [94](1[94] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 10)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[93] + 0 + 0 + [93](1[93] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 11)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[92] + 0 + 0 + [92](1[92] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 12)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[91] + 0 + 0 + [91](1[91] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 13)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[90] + 0 + 0 + [90](1[90] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 14)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[63] + 0 + 0 + [63](1[63] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 15)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[62] + 0 + 0 + [62](1[62] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 16)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[61] + 0 + 0 + [61](1[61] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 17)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[60] + 0 + 0 + [60](1[60] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 18)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[59] + 0 + 0 + [59](1[59] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 19)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[16] + 0 + 0 + [16](1[16] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 20)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[9] + 0 + 0 + [9](1[9] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 21)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[58] + 0 + 0 + [58](1[58] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 22)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[57] + 0 + 0 + [57](1[57] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 23)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[56] + 0 + 0 + [56](1[56] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 24)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[55] + 0 + 0 + [55](1[55] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 25)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[54] + 0 + 0 + [54](1[54] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 26)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[53] + 0 + 0 + [53](1[53] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 27)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[52] + 0 + 0 + [52](1[52] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 28)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[51] + 0 + 0 + [51](1[51] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 29)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[50] + 0 + 0 + [50](1[50] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 30)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[49] + 0 + 0 + [49](1[49] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 31)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[48] + 0 + 0 + [48](1[48] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 32)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[47] + 0 + 0 + [47](1[47] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 33)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[46] + 0 + 0 + [46](1[46] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 34)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[45] + 0 + 0 + [45](1[45] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 35)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[44] + 0 + 0 + [44](1[44] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 36)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[43] + 0 + 0 + [43](1[43] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 37)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 15360 + 3840[24] + -1[25] + -3840[28] + 1[29] + 0 + 0 + 0
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 38)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 235944960 + 117968640[24] + -117968640[28] + 0 + 0 + [24](14745600[24] + -29491200[28] + 0 + 0) + [28](14745600[28] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 39)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[43] + 1[44] + 1[45] + 1[46] + 1[47] + 1[48] + 1[49] + 1[50] + 1[51] + 1[52] + 1[53] + 1[54] + 1[55] + 1[56] + 1[57] + 1[58] + 1[9] + 1[16] + [43](-1[21] + 0 + 0) + [44](-1[21] + 0 + 0) + [45](-1[21] + 0 + 0) + [46](-1[21] + 0 + 0) + [47](-1[21] + 0 + 0) + [48](-1[21] + 0 + 0) + [49](-1[21] + 0 + 0) + [50](-1[21] + 0 + 0) + [51](-1[21] + 0 + 0) + [52](-1[21] + 0 + 0) + [53](-1[21] + 0 + 0) + [54](-1[21] + 0 + 0) + [55](-1[21] + 0 + 0) + [56](-1[21] + 0 + 0) + [57](-1[21] + 0 + 0) + [58](-1[21] + 0 + 0) + [9](-1[21] + 0 + 0) + [16](-1[21] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 40)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[96] + 0 + 0 + [43](-1[21] + 0 + 0) + [44](-1[21] + 0 + 0) + [45](-1[21] + 0 + 0) + [46](-1[21] + 0 + 0) + [47](-1[21] + 0 + 0) + [48](-1[21] + 0 + 0) + [49](-1[21] + 0 + 0) + [50](-1[21] + 0 + 0) + [51](-1[21] + 0 + 0) + [52](-1[21] + 0 + 0) + [53](-1[21] + 0 + 0) + [54](-1[21] + 0 + 0) + [55](-1[21] + 0 + 0) + [57](-1[21] + 0 + 0) + [58](-1[21] + 0 + 0) + [9](-1[21] + 0 + 0) + [16](-1[21] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 41)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [94](1[95] + 0 + 0) + [95](1[23] + -1[27] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 42)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 2^2[95] + 0 + 0 + [94](-65536[95] + 0 + 0) + [95](1[22] + -1[26] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 43)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[95] + -1[21] + 0 + 0 + [52](1[21] + 0 + 0) + [53](1[21] + 0 + 0) + [54](1[21] + 0 + 0) + [55](1[21] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 44)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [62](1[16] + 0 + 0) + [63](1[16] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 45)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [62](1[16] + 0 + 0) + [63](2[16] + 0 + 0) + [85](2^2[16] + 0 + 0) + [16](-1[17] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 46)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[93] + 0 + 0 + [61](-1[9] + -1[16] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 47)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [61](1[16] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 48)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [65](1[16] + 0 + 0) + [16](-1[18] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 49)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [65](1[9] + 0 + 0) + [9](-1[11] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 50)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [64](1[16] + 0 + 0) + [16](-1[17] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 51)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [64](1[9] + 0 + 0) + [9](-1[10] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 52)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [41](1[9] + 1[16] + 0 + 0) + [59](1[9] + 1[16] + 0 + 0) + [60](-65536[9] + -65536[16] + 0 + 0) + [3](1[9] + 1[16] + 0 + 0) + [9](-1[11] + 0 + 0) + [16](-1[18] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 53)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [40](1[9] + 1[16] + 0 + 0) + [59](-65536[9] + -65536[16] + 0 + 0) + [2](1[9] + 1[16] + 0 + 0) + [9](-1[10] + 0 + 0) + [16](-1[17] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 54)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[18] + 0 + 0 + [16](-1[18] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 55)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[39] + 1[17] + 0 + 0 + [39](1[16] + 0 + 0) + [16](-1[17] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 56)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[11] + 0 + 0 + [9](-1[11] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 57)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[38] + 1[10] + 0 + 0 + [38](1[9] + 0 + 0) + [9](-1[10] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 58)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [57](1[67] + 2^8[68] + 1[71] + 2^8[72] + 1[75] + 2^8[76] + 1[79] + 2^8[80] + -1[20] + 0) + [58](1[67] + 2^8[68] + -1[20] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 59)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [57](1[65] + 2^8[66] + 1[69] + 2^8[70] + 1[73] + 2^8[74] + 1[77] + 2^8[78] + -1[19] + 0) + [58](1[65] + 2^8[66] + -1[19] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 60)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[57] + -1[58] + 0 + 0 + [57](1[57] + 2[58] + 0 + 0) + [58](1[58] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 61)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [92](1[20] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 62)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [92](1[19] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 63)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [91](1[20] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 64)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [86](1[90] + 0 + 0) + [90](-1[20] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 65)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [66](1[91] + 0 + 0) + [85](1[90] + 0 + 0) + [90](-1[19] + 0 + 0) + [91](-1[19] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 66)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[92] + 0 + 0 + [52](-1[56] + 0 + 0) + [53](-1[56] + 0 + 0) + [54](-1[56] + 0 + 0) + [55](-1[56] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 67)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[54] + 1[91] + 0 + 0 + [54](1[56] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 68)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[52] + -1[53] + 1[90] + 0 + 0 + [52](1[56] + 0 + 0) + [53](1[56] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 69)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [52](1[63] + 0 + 0) + [53](1[63] + 0 + 0) + [63](1[89] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 70)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [41](1[52] + 1[53] + 1[89] + 0 + 0) + [52](1[61] + -65536[62] + 1[23] + -1[27] + 0 + 0) + [53](1[61] + -65536[62] + 1[3] + -1[27] + 0 + 0) + [54](1[61] + -65536[62] + 1[23] + -1[27] + 0 + 0) + [55](1[61] + -65536[62] + 1[23] + -1[27] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 71)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 2^2[54] + 2^2[55] + -4[89] + 0 + 0 + [40](1[52] + 1[53] + 1[89] + 0 + 0) + [52](-65536[61] + -1[88] + 1[22] + 0 + 0) + [53](-65536[61] + -1[88] + 1[2] + 0 + 0) + [54](-65536[61] + -1[88] + 1[22] + 0 + 0) + [55](-65536[61] + -1[88] + 1[22] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 72)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[89] + 0 + 0 + [55](1[66] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 73)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [41](1[54] + 0 + 0) + [52](1[59] + -65536[60] + -1[86] + 1[23] + 0 + 0) + [53](1[59] + -65536[60] + -1[86] + 1[23] + 0 + 0) + [54](1[59] + -65536[60] + 1[86] + -1[3] + 1[8] + 0 + 0) + [55](1[59] + -65536[60] + 1[86] + -1[3] + 1[8] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 74)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 2^2[52] + 2^2[53] + 0 + 0 + [40](1[54] + 0 + 0) + [52](-65536[59] + -1[85] + 1[22] + 0 + 0) + [53](-65536[59] + -1[85] + 1[22] + 0 + 0) + [54](-65536[59] + 1[85] + -1[2] + 1[7] + 0 + 0) + [55](-65536[59] + 1[85] + -1[2] + 1[7] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 75)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [50](1[20] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 76)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [50](1[19] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 77)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [50](1[6] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 78)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [50](1[5] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 79)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [50](1[8] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 80)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [50](1[7] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 81)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 30720[46] + 30720[47] + 30720[48] + 30720[49] + 0 + 0 + [41](1[43] + 1[45] + 0 + 0) + [43](-65536[59] + 1[60] + 1[3] + 1[8] + -1[20] + 0 + 0) + [44](-65536[59] + 1[60] + -1[3] + 1[8] + 1[20] + 0 + 0) + [45](-65536[59] + 1[60] + -1[20] + 1[23] + 0 + 0) + [46](-65536[59] + 1[60] + 1[86] + -1[20] + 0 + 0) + [47](-65536[59] + 1[60] + 1[86] + -1[20] + 0 + 0) + [48](-65536[59] + 1[60] + 1[86] + -1[20] + 0 + 0) + [49](-65536[59] + 1[60] + 1[86] + -1[20] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 82)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[46] + 1[47] + 1[48] + 1[49] + 0 + 0 + [40](1[43] + 1[45] + 0 + 0) + [43](-65536[60] + 1[2] + 1[7] + -1[19] + 0 + 0) + [44](-65536[60] + -1[2] + 1[7] + 1[19] + 0 + 0) + [45](-65536[60] + -1[19] + 1[22] + 0 + 0) + [46](-65536[60] + 1[85] + -1[19] + 0 + 0) + [47](-65536[60] + 1[85] + -1[19] + 0 + 0) + [48](-65536[60] + 1[85] + -1[19] + 0 + 0) + [49](-65536[60] + 1[85] + -1[19] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 83)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 1[46] + 1[47] + 1[48] + 1[49] + 0 + 0 + [46](-1[59] + 0 + 0) + [47](-1[59] + 0 + 0) + [48](-1[59] + 0 + 0) + [49](-1[59] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 84)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + 0 + 0 + 0 + [46](-1[2] + -65536[3] + -1[7] + -65536[8] + 1[19] + 2^16[20] + 0 + 0) + [47](-1[2] + -65536[3] + 1[7] + 2^16[8] + 1[19] + 2^16[20] + 0 + 0) + [48](-1[87] + 1[19] + 2^16[20] + 0 + 0) + [49](-1[87] + 1[19] + 2^16[20] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 85)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[87] + 0 + 0 + [49](1[14] + 2^16[15] + 0 + 0) + [2](943718400[7] + -30720[8] + 0 + 0) + [3](-30720[7] + 1[8] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 86)
    
    // EnforceSingleMaxQuadraticConstraint: 0 == 0 + -1[21] + 0 + 0 + [21](1[21] + 0 + 0)
    acc := gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, 87)
    
    // LookupWithDensAndSetupExpressions: [21]/(δ + β⁰(0 + 1[22] + 0 + 0) + β¹(0 + 1[23] + 0 + 0) + β²(0 + 1[4] + 0 + 0) + β³(0 + 1[38] + 0 + 0) + β⁴(0 + 1[39] + 0 + 0) + β⁵(0 + 1[40] + 0 + 0) + β⁶(0 + 1[41] + 0 + 0) + β⁷(0 + 1[42] + 0 + 0) + β⁸(0 + 1[43] + 2[44] + 2^2[45] + 2^3[46] + 2^4[47] + 2^5[48] + 2^6[49] + 2^7[50] + 2^8[51] + 2^9[52] + 2^10[53] + 2^11[54] + 2^12[55] + 2^13[56] + 2^14[57] + 2^15[58] + 2^16[9] + 2^17[16]) + β⁹(46 + 0 + 0 + 0)) - [102]/(δ + β⁰[103] + β¹[104] + β²[105] + β³[106] + β⁴[107] + β⁵[108] + β⁶[109] + β⁷[110] + β⁸[111] + β⁹[112]) = [70]/[71]
    acc := gate_lookupwithdensandsetupexpressions(ptr, alpha, acc, 21, 102, 88, add(112, shl(7, add(111, shl(7, add(110, shl(7, add(109, shl(7, add(108, shl(7, add(107, shl(7, add(106, shl(7, add(105, shl(7, add(104, shl(7, 103)))))))))))))))))))
    
    // MaterializeSingleLookupInput: 2^19 + -1[25] + 1[13] + -1[99] + 0 + 0 = [69]
    acc := gate_materializesinglelookupinput(ptr, alpha, acc, 89)
    
    // LookupPairFromBaseInputs: 1/(δ + 2^19 + -1[25] + 1[6] + -1[98] + 0 + 0) + 1/(δ + -2 + -1[24] + 1[12] + 2^19[99] + 0 + 0) = [67]/[68]
    acc := gate_lookuppairfrombaseinputs(ptr, alpha, acc, 90, 91)
    
    // LookupPairFromBaseInputs: 1/(δ + 2^19 + -1[25] + 1[1] + -1[97] + 0 + 0) + 1/(δ + -1 + -1[24] + 1[5] + 2^19[98] + 0 + 0) = [65]/[66]
    acc := gate_lookuppairfrombaseinputs(ptr, alpha, acc, 92, 93)
    
    // LookupPairFromBaseInputs: 1/(δ + 0 + 1[29] + 0 + 0) + 1/(δ + 0 + -1[24] + 1[0] + 2^19[97] + 0 + 0) = [63]/[64]
    acc := gate_lookuppairfrombaseinputs(ptr, alpha, acc, 94, 95)
    
    // LookupFromMaterializedBaseInputWithSetup: 1/(δ + [28]) - [101]/(δ + Cache(1)) = [61]/[62]
    acc := gate_lookupfrommaterializedbaseinputwithsetup(ptr, alpha, acc, 101, 28, 1)
    
    // CopyInBaseField: [27] = [60]
    acc := gate_copyinbasefield(ptr, alpha, acc, 27)
    
    // LookupPairFromBaseInputs: 1/(δ + 0 + 1[18] + 0 + 0) + 1/(δ + 0 + 1[26] + 0 + 0) = [58]/[59]
    acc := gate_lookuppairfrombaseinputs(ptr, alpha, acc, 96, 97)
    
    // LookupPairFromBaseInputs: 1/(δ + 0 + 1[11] + 0 + 0) + 1/(δ + 0 + 1[17] + 0 + 0) = [56]/[57]
    acc := gate_lookuppairfrombaseinputs(ptr, alpha, acc, 98, 99)
    
    // LookupPairFromBaseInputs: 1/(δ + 0 + 1[88] + 0 + 0) + 1/(δ + 0 + 1[10] + 0 + 0) = [54]/[55]
    acc := gate_lookuppairfrombaseinputs(ptr, alpha, acc, 100, 101)
    
    // LookupPairFromBaseInputs: 1/(δ + 0 + 1[20] + 0 + 0) + 1/(δ + 0 + 1[23] + 0 + 0) = [52]/[53]
    acc := gate_lookuppairfrombaseinputs(ptr, alpha, acc, 102, 103)
    
    // LookupPairFromBaseInputs: 1/(δ + 0 + 1[86] + 0 + 0) + 1/(δ + 0 + 1[19] + 0 + 0) = [50]/[51]
    acc := gate_lookuppairfrombaseinputs(ptr, alpha, acc, 104, 105)
    
    // LookupFromMaterializedBaseInputWithSetup: 1/(δ + [85]) - [100]/(δ + Cache(0)) = [48]/[49]
    acc := gate_lookupfrommaterializedbaseinputwithsetup(ptr, alpha, acc, 100, 85, 0)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[80] + 0 + 0) = [47]
    acc := gate_maxquadratic(ptr, alpha, acc, 106)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[79] + 0 + 0) = [46]
    acc := gate_maxquadratic(ptr, alpha, acc, 107)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[78] + 0 + 0) = [45]
    acc := gate_maxquadratic(ptr, alpha, acc, 108)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[77] + 0 + 0) = [44]
    acc := gate_maxquadratic(ptr, alpha, acc, 109)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [42](1[57] + 0 + 0) = [43]
    acc := gate_maxquadratic(ptr, alpha, acc, 110)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [40](1[57] + 0 + 0) + [57](1[64] + 0 + 0) + [58](1[68] + 0 + 0) = [42]
    acc := gate_maxquadratic(ptr, alpha, acc, 111)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](7864320[82] + -7864320[3] + 0 + 0) + [58](1[64] + 7864320[84] + -7864320[8] + 0 + 0) = [41]
    acc := gate_maxquadratic(ptr, alpha, acc, 112)
    
    // MaxQuadratic: 0 + 3[57] + 0 + 0 + [58](7864320[82] + -7864320[3] + 0 + 0) = [40]
    acc := gate_maxquadratic(ptr, alpha, acc, 113)
    
    // MaxQuadratic: 0 + 9[57] + 0 + 0 + [42](1[58] + 0 + 0) = [39]
    acc := gate_maxquadratic(ptr, alpha, acc, 114)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[76] + 0 + 0) = [38]
    acc := gate_maxquadratic(ptr, alpha, acc, 115)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[75] + 0 + 0) = [37]
    acc := gate_maxquadratic(ptr, alpha, acc, 116)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[74] + 0 + 0) = [36]
    acc := gate_maxquadratic(ptr, alpha, acc, 117)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[73] + 0 + 0) = [35]
    acc := gate_maxquadratic(ptr, alpha, acc, 118)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [42](1[57] + 0 + 0) = [34]
    acc := gate_maxquadratic(ptr, alpha, acc, 119)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [40](1[57] + 0 + 0) + [52](1[26] + 0 + 0) + [53](1[26] + 0 + 0) + [54](1[26] + 0 + 0) + [55](1[26] + 0 + 0) + [57](1[64] + 0 + 0) + [58](1[67] + 0 + 0) = [33]
    acc := gate_maxquadratic(ptr, alpha, acc, 120)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [52](1[63] + 0 + 0) + [53](1[63] + 0 + 0) + [54](1[63] + 0 + 0) + [55](1[63] + 0 + 0) + [57](1[82] + 0 + 0) + [58](1[64] + 1[84] + 0 + 0) = [32]
    acc := gate_maxquadratic(ptr, alpha, acc, 121)
    
    // MaxQuadratic: 0 + 2[57] + 0 + 0 + [52](1[88] + 0 + 0) + [53](1[88] + 0 + 0) + [54](1[88] + 0 + 0) + [55](1[88] + 0 + 0) + [58](1[82] + 0 + 0) = [31]
    acc := gate_maxquadratic(ptr, alpha, acc, 122)
    
    // MaxQuadratic: 0 + 2[52] + 2[53] + 2[54] + 2[55] + 9[57] + 0 + 0 + [42](1[58] + 0 + 0) = [30]
    acc := gate_maxquadratic(ptr, alpha, acc, 123)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[72] + 0 + 0) = [29]
    acc := gate_maxquadratic(ptr, alpha, acc, 124)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[71] + 0 + 0) = [28]
    acc := gate_maxquadratic(ptr, alpha, acc, 125)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[70] + 0 + 0) = [27]
    acc := gate_maxquadratic(ptr, alpha, acc, 126)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[69] + 0 + 0) = [26]
    acc := gate_maxquadratic(ptr, alpha, acc, 127)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [42](1[57] + 0 + 0) = [25]
    acc := gate_maxquadratic(ptr, alpha, acc, 128)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [40](1[57] + 0 + 0) + [57](1[64] + 0 + 0) + [58](1[66] + 0 + 0) = [24]
    acc := gate_maxquadratic(ptr, alpha, acc, 129)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [41](1[58] + 0 + 0) + [52](1[66] + 0 + 0) + [53](1[66] + 0 + 0) + [54](1[66] + 0 + 0) + [55](1[66] + 0 + 0) + [57](7864320[81] + -7864320[2] + 0 + 0) + [58](7864320[83] + -7864320[7] + 0 + 0) = [23]
    acc := gate_maxquadratic(ptr, alpha, acc, 130)
    
    // MaxQuadratic: 0 + 1[57] + 0 + 0 + [42](2^19[52] + 2^19[53] + 2^19[54] + 2^19[55] + 0 + 0) + [52](2^17[60] + 2^18[64] + 2^16[65] + 1[8] + 0 + 0) + [53](2^17[60] + 2^18[64] + 2^16[65] + 1[8] + 0 + 0) + [54](2^17[60] + 2^18[64] + 2^16[65] + 1[8] + 0 + 0) + [55](2^17[60] + 2^18[64] + 2^16[65] + 1[8] + 0 + 0) + [58](7864320[81] + -7864320[2] + 0 + 0) = [22]
    acc := gate_maxquadratic(ptr, alpha, acc, 131)
    
    // MaxQuadratic: 0 + 31[52] + 31[53] + 31[54] + 31[55] + 9[57] + 0 + 0 + [42](1[58] + 0 + 0) = [21]
    acc := gate_maxquadratic(ptr, alpha, acc, 132)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[68] + 0 + 0) = [20]
    acc := gate_maxquadratic(ptr, alpha, acc, 133)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[67] + 0 + 0) = [19]
    acc := gate_maxquadratic(ptr, alpha, acc, 134)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[66] + 0 + 0) = [18]
    acc := gate_maxquadratic(ptr, alpha, acc, 135)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[65] + 0 + 0) = [17]
    acc := gate_maxquadratic(ptr, alpha, acc, 136)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [42](1[57] + 0 + 0) = [16]
    acc := gate_maxquadratic(ptr, alpha, acc, 137)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [40](1[57] + 0 + 0) + [57](1[64] + 0 + 0) + [58](1[65] + 0 + 0) = [15]
    acc := gate_maxquadratic(ptr, alpha, acc, 138)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [40](1[58] + 0 + 0) + [52](1[65] + 0 + 0) + [53](1[65] + 0 + 0) + [54](1[65] + 0 + 0) + [55](1[65] + 0 + 0) + [57](1[81] + 0 + 0) + [58](1[83] + 0 + 0) = [14]
    acc := gate_maxquadratic(ptr, alpha, acc, 139)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [52](1[3] + 0 + 0) + [53](1[3] + 0 + 0) + [54](1[3] + 0 + 0) + [55](1[3] + 0 + 0) + [58](1[81] + 0 + 0) = [13]
    acc := gate_maxquadratic(ptr, alpha, acc, 140)
    
    // MaxQuadratic: 0 + 5[52] + 5[53] + 5[54] + 5[55] + 9[57] + 0 + 0 + [42](1[58] + 0 + 0) = [12]
    acc := gate_maxquadratic(ptr, alpha, acc, 141)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [57](1[64] + 0 + 0) + [8](1[93] + 0 + 0) + [9](-1[8] + 1[20] + 0 + 0) + [16](-1[8] + 1[20] + 0 + 0) = [11]
    acc := gate_maxquadratic(ptr, alpha, acc, 142)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [52](1[64] + 0 + 0) + [53](1[64] + 0 + 0) + [54](1[64] + 0 + 0) + [55](1[64] + 0 + 0) + [57](7864320[83] + -7864320[7] + 0 + 0) + [58](1[64] + 0 + 0) + [7](1[93] + 0 + 0) + [9](-1[7] + 1[19] + 0 + 0) + [16](-1[7] + 1[19] + 0 + 0) = [10]
    acc := gate_maxquadratic(ptr, alpha, acc, 143)
    
    // MaxQuadratic: 0 + 0 + 0 + 0 + [41](1[58] + 0 + 0) + [52](1[85] + 1[86] + 0 + 0) + [53](1[85] + 1[86] + 0 + 0) + [54](1[85] + 1[86] + 0 + 0) + [55](1[85] + 1[86] + 0 + 0) + [57](1[83] + 0 + 0) + [64](1[93] + 0 + 0) + [65](2^16[93] + 0 + 0) = [9]
    acc := gate_maxquadratic(ptr, alpha, acc, 144)
    
    // MaxQuadratic: 0 + 1[52] + 1[53] + 1[54] + 1[55] + 2^3[57] + 3[58] + 0 + 0 + [21](34[93] + 0 + 0) = [8]
    acc := gate_maxquadratic(ptr, alpha, acc, 145)
    
    // MaxQuadratic: 0 + -64[9] + -64[16] + 0 + 0 + [9](2^16[61] + 1[65] + 0 + 0) + [16](2^16[61] + 1[65] + 0 + 0) = [7]
    acc := gate_maxquadratic(ptr, alpha, acc, 146)
    
    // InitsOrTeardownsInitialPair: (γ + 1 + αCache(2) + α²(Cache(3) + 0) + α³[32] + α⁴[33] + α⁵[30] + α⁶[31]) * (γ + 1 + αCache(2) + α²(Cache(3) + 1024) + α³[36] + α⁴[37] + α⁵[34] + α⁶[35]) = [6]
    acc := gate_initsorteardownsinitialpair(ptr, alpha, acc, 2, 3, add(0, shl(8, 1)), add(1, shl(1, add(32, shl(7, add(33, shl(7, add(30, shl(7, 31)))))))), add(1, shl(1, add(36, shl(7, add(37, shl(7, add(34, shl(7, 35)))))))))
    
    // InitsOrTeardownsInitialPair: (γ + 1 + αCache(2) + α²(Cache(3) + 0) + 0) * (γ + 1 + αCache(2) + α²(Cache(3) + 1024) + 0) = [5]
    acc := gate_initsorteardownsinitialpair(ptr, alpha, acc, 2, 3, add(0, shl(8, 1)), shl(1, 0), shl(1, 0))
    
    // InitialGrandProductWithoutCaches: (γ + [16] + α[17] + α²[18] + α³(2 + [24]) + α⁴[25] + α⁵[19] + α⁶[20])*(γ + 2 + α0 + α²0 + α³(0 + [28]) + α⁴[29] + α⁵[26] + α⁶[27]) = [4]
    acc := gate_initialgrandproductwithoutcaches(ptr, alpha, acc, add(add(1, shl(1, 16)), shl(9, add(add(1, shl(1, add(17, shl(7, add(1, shl(1, 18)))))), shl(17, add(add(1, shl(1, add(2, shl(2, add(24, shl(7, 25)))))), shl(17, add(1, shl(2, add(19, shl(7, 20)))))))))), add(shl(1, 2), shl(9, add(shl(1, 0), shl(17, add(add(1, shl(1, add(0, shl(2, add(28, shl(7, 29)))))), shl(17, add(1, shl(2, add(26, shl(7, 27)))))))))))
    
    // InitialGrandProductWithoutCaches: (γ + [16] + α[17] + α²[18] + α³(0 + [12]) + α⁴[13] + α⁵[14] + α⁶[15])*(γ + 2 + α0 + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[22] + α⁶[23]) = [3]
    acc := gate_initialgrandproductwithoutcaches(ptr, alpha, acc, add(add(1, shl(1, 16)), shl(9, add(add(1, shl(1, add(17, shl(7, add(1, shl(1, 18)))))), shl(17, add(add(1, shl(1, add(0, shl(2, add(12, shl(7, 13)))))), shl(17, add(1, shl(2, add(14, shl(7, 15)))))))))), add(shl(1, 2), shl(9, add(shl(1, 0), shl(17, add(add(1, shl(1, add(0, shl(2, add(24, shl(7, 25)))))), shl(17, add(1, shl(2, add(22, shl(7, 23)))))))))))
    
    // InitialGrandProductWithoutCaches: (γ + 0 + α[4] + α²0 + α³(0 + [24]) + α⁴[25] + α⁵[2] + α⁶[3])*(γ + [9] + α[10] + α²[11] + α³(1 + [24]) + α⁴[25] + α⁵[7] + α⁶[8]) = [2]
    acc := gate_initialgrandproductwithoutcaches(ptr, alpha, acc, add(shl(1, 0), shl(9, add(add(1, shl(1, 4)), shl(17, add(add(1, shl(1, add(0, shl(2, add(24, shl(7, 25)))))), shl(17, add(1, shl(2, add(2, shl(7, 3)))))))))), add(add(1, shl(1, 9)), shl(9, add(add(1, shl(1, add(10, shl(7, add(1, shl(1, 11)))))), shl(17, add(add(1, shl(1, add(1, shl(2, add(24, shl(7, 25)))))), shl(17, add(1, shl(2, add(7, shl(7, 8)))))))))))
    
    // InitialGrandProductWithoutCaches: (γ + 0 + α[4] + α²0 + α³(0 + [0]) + α⁴[1] + α⁵[2] + α⁶[3])*(γ + [9] + α[10] + α²[11] + α³(0 + [5]) + α⁴[6] + α⁵[7] + α⁶[8]) = [1]
    acc := gate_initialgrandproductwithoutcaches(ptr, alpha, acc, add(shl(1, 0), shl(9, add(add(1, shl(1, 4)), shl(17, add(add(1, shl(1, add(0, shl(2, add(0, shl(7, 1)))))), shl(17, add(1, shl(2, add(2, shl(7, 3)))))))))), add(add(1, shl(1, 9)), shl(9, add(add(1, shl(1, add(10, shl(7, add(1, shl(1, 11)))))), shl(17, add(add(1, shl(1, add(0, shl(2, add(5, shl(7, 6)))))), shl(17, add(1, shl(2, add(7, shl(7, 8)))))))))))
    
    // CopyInBaseField: [21] = [0]
    acc := gate_copyinbasefield(ptr, alpha, acc, 21)
    
    let rhs_scaled := mulmod(acc, eq_scale, P)
    // TODO: benchmark canonical claim updates so scaled checks can use plain eq.
    // after stack-heavy values are dead
    if mod(add(claim, sub(P, rhs_scaled)), P) { revert(0, 0) }


    // POINT CLAIMS BATCH (113 POINTS)
    next_ptr, next_claim, next_alpha := sumcheck_claims_batch(ptr, 113)
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
    let seed := keccak256(SEED_PTR(), add(32, input_bytes))
    mstore(SEED_PTR(), seed)
    alpha := shr(128, seed)
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

// function gkr_memrel_compress_low(address_space, addr_low, addr_high) -> compressed {
//     compressed := add(compressed, add(mload(add(MEMORY_CHALLS_PTR(), 192)), address_space))
//     compressed := add(compressed, mulmod(mload(MEMORY_CHALLS_PTR()), addr_low, P))
//     compressed := add(compressed, mulmod(mload(add(MEMORY_CHALLS_PTR(), 32)), addr_high, P))
// }
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

function gate_calldataload(ptr, idx) -> load {
    load := shr(128, calldataload(add(ptr, mul(16, idx))))
}
function gate_mload(ptr, idx) -> load {
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
function memory_gamma() -> gamma {
    gamma := mload(add(MEMORY_CHALLS_PTR(), mul(32, 6)))
}
function memory_alpha1() -> alpha1 {
    alpha1 := mload(add(MEMORY_CHALLS_PTR(), mul(32, 0)))
}
function memory_alpha2() -> alpha2 {
    alpha2 := mload(add(MEMORY_CHALLS_PTR(), mul(32, 1)))
}
function memory_alpha3() -> alpha3 {
    alpha3 := mload(add(MEMORY_CHALLS_PTR(), mul(32, 2)))
}
function memory_alpha4() -> alpha4 {
    alpha4 := mload(add(MEMORY_CHALLS_PTR(), mul(32, 3)))
}
function memory_alpha5() -> alpha5 {
    alpha5 := mload(add(MEMORY_CHALLS_PTR(), mul(32, 4)))
}
function memory_alpha6() -> alpha6 {
    alpha6 := mload(add(MEMORY_CHALLS_PTR(), mul(32, 5)))
}
function logup_gamma() -> gamma {
    gamma := mload(add(LOGUP_CHALLS_PTR(), 32))
}
function logup_alpha() -> alpha {
    alpha := mload(LOGUP_CHALLS_PTR())
}
function linterm_to_calldata(ptr, modc, sign, var_idx) -> term {
    let input := gate_calldataload(ptr, var_idx)
    if sign {
        input := u128_neg(input)
    }
    term := mul(modc, input)
}
function linterms6_from_pack(ptr, pack) -> linear {
    let n := and(pack, sub(shl(3, 1), 1))
    pack := shr(3, pack)
    for { let i := 0 } lt(i, n) { i := add(i, 1) } {
        let var_idx := and(pack, sub(shl(7, 1), 1))
        pack := shr(7, pack)
        let modc := and(pack, sub(shl(30, 1), 1))
        pack := shr(30, pack)
        let sign := and(pack, 1)
        let term := linterm_to_calldata(ptr, modc, sign, var_idx)
        linear := add(linear, term)
        pack := shr(1, pack)
    }
}
function linterms18_from_pack(ptr, pack1, pack2, pack3) -> linear {
    linear := add(linear, linterms6_from_pack(ptr, pack1))
    linear := add(linear, linterms6_from_pack(ptr, pack2))
    linear := add(linear, linterms6_from_pack(ptr, pack3))
}
function linrel_from_pack(ptr, const, pack1, pack2, pack3) -> linear {
    let sign := shr(30, const)
    if sign {
        let modc := and(const, sub(shl(30, 1), 1))
        const := sub(P, modc)
    }
    linear := add(const, linterms18_from_pack(ptr, pack1, pack2, pack3))
}
function quadrel_from_pack(ptr, var_idx, pack1, pack2, pack3) -> quadratic {
    let var := gate_calldataload(ptr, var_idx)
    quadratic := mulmod(var, linterms18_from_pack(ptr, pack1, pack2, pack3), P)
}
function linrel_from_cfg(ptr, id) -> value {
    let const, pack1, pack2, pack3 := cfg(id, 0)
    value := linrel_from_pack(ptr, const, pack1, pack2, pack3)
}
function lookrelsingle_from_cfg(ptr, id) -> value {
    let const, pack1, pack2, pack3 := cfg(id, 0)
    value := add(logup_gamma(), linrel_from_pack(ptr, const, pack1, pack2, pack3))
}
function lookrelgeneric_from_cfg(ptr, id) -> value {
    for { let i := 9 } lt(i, 10) { i := sub(i, 1) } {
        let const, pack1, pack2, pack3 := cfg(id, i)
        value := add(mulmod(value, logup_alpha(), P), linrel_from_pack(ptr, const, pack1, pack2, pack3))
    }
    value := add(value, logup_gamma())
}
function quadrel_from_cfg(ptr, id) -> value {
    let dyn_const, pack1, pack2, pack3 := cfg(id, 0)
    let const := and(dyn_const, sub(shl(31, 1), 1))
    let top_bit := shr(31, dyn_const)
    value := linrel_from_pack(ptr, const, pack1, pack2, pack3)
    for { let i := 1 } top_bit { i := add(i, 1) } {
        let dyn_var_idx
        dyn_var_idx, pack1, pack2, pack3 := cfg(id, i)
        top_bit := shr(7, dyn_var_idx)
        let var_idx := and(dyn_var_idx, sub(shl(7, 1), 1))
        value := add(value, quadrel_from_pack(ptr, var_idx, pack1, pack2, pack3))
    }
}
// this fn is for fetching dynamic inputs
function cfg(id, item) -> meta, pack1, pack2, pack3 {
    switch id
    case 0 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(40, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 0 pack1 := add(1, shl(3, add(41, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 0 pack1 := add(1, shl(3, add(42, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := 0 pack1 := add(1, shl(3, add(43, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := 0 pack1 := add(1, shl(3, add(44, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 5 { meta := 0 pack1 := add(1, shl(3, add(45, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 6 { meta := 0 pack1 := add(1, shl(3, add(46, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 7 { meta := 0 pack1 := add(1, shl(3, add(47, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 8 { meta := 0 pack1 := 0 pack2 := 0 pack3 := 0 }
        case 9 { meta := 0 pack1 := add(1, shl(3, add(39, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 1 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(22, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 0 pack1 := add(1, shl(3, add(23, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 0 pack1 := add(1, shl(3, add(24, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := 0 pack1 := add(1, shl(3, add(25, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := 0 pack1 := add(1, shl(3, add(26, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 5 { meta := 0 pack1 := add(1, shl(3, add(27, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 6 { meta := 0 pack1 := add(1, shl(3, add(28, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 7 { meta := 0 pack1 := add(1, shl(3, add(29, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 8 { meta := 0 pack1 := 0 pack2 := 0 pack3 := 0 }
        case 9 { meta := 0 pack1 := add(1, shl(3, add(21, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 2 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(31, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 0 pack1 := add(1, shl(3, add(32, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 0 pack1 := add(1, shl(3, add(33, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := 0 pack1 := add(1, shl(3, add(34, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := 0 pack1 := add(1, shl(3, add(35, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 5 { meta := 0 pack1 := add(1, shl(3, add(36, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 6 { meta := 0 pack1 := add(1, shl(3, add(37, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 7 { meta := 0 pack1 := add(1, shl(3, add(38, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 8 { meta := 0 pack1 := 0 pack2 := 0 pack3 := 0 }
        case 9 { meta := 0 pack1 := add(1, shl(3, add(30, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 3 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(9, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 0 pack1 := add(1, shl(3, add(10, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 0 pack1 := add(1, shl(3, add(11, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := 0 pack1 := 0 pack2 := 0 pack3 := 0 }
        case 4 { meta := 0 pack1 := 0 pack2 := 0 pack3 := 0 }
        case 5 { meta := 0 pack1 := 0 pack2 := 0 pack3 := 0 }
        case 6 { meta := 0 pack1 := 0 pack2 := 0 pack3 := 0 }
        case 7 { meta := 0 pack1 := 0 pack2 := 0 pack3 := 0 }
        case 8 { meta := 0 pack1 := 0 pack2 := 0 pack3 := 0 }
        case 9 { meta := 0 pack1 := add(1, shl(3, add(8, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 4 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(13, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 0 pack1 := add(1, shl(3, add(14, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 0 pack1 := add(1, shl(3, add(15, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := 0 pack1 := add(1, shl(3, add(16, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := 0 pack1 := add(1, shl(3, add(17, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 5 { meta := 0 pack1 := add(1, shl(3, add(18, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 6 { meta := 0 pack1 := add(1, shl(3, add(19, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 7 { meta := 0 pack1 := add(1, shl(3, add(20, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 8 { meta := 0 pack1 := 0 pack2 := 0 pack3 := 0 }
        case 9 { meta := 0 pack1 := add(1, shl(3, add(12, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 5 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(99, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 99 pack1 := add(1, shl(3, add(99, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 6 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(98, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 98 pack1 := add(1, shl(3, add(98, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 7 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(97, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 97 pack1 := add(1, shl(3, add(97, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 8 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(96, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 96 pack1 := add(1, shl(3, add(96, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 9 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(95, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 95 pack1 := add(1, shl(3, add(95, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 10 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(94, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 94 pack1 := add(1, shl(3, add(94, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 11 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(93, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 93 pack1 := add(1, shl(3, add(93, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 12 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(92, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 92 pack1 := add(1, shl(3, add(92, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 13 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(91, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 91 pack1 := add(1, shl(3, add(91, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 14 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(90, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 90 pack1 := add(1, shl(3, add(90, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 15 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(63, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 63 pack1 := add(1, shl(3, add(63, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 16 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(62, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 62 pack1 := add(1, shl(3, add(62, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 17 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(61, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 61 pack1 := add(1, shl(3, add(61, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 18 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(60, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 60 pack1 := add(1, shl(3, add(60, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 19 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(59, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 59 pack1 := add(1, shl(3, add(59, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 20 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(16, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 16 pack1 := add(1, shl(3, add(16, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 21 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(9, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 9 pack1 := add(1, shl(3, add(9, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 22 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(58, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 58 pack1 := add(1, shl(3, add(58, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 23 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(57, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(57, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 24 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(56, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 56 pack1 := add(1, shl(3, add(56, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 25 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(55, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 55 pack1 := add(1, shl(3, add(55, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 26 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(54, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 54 pack1 := add(1, shl(3, add(54, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 27 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(53, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 53 pack1 := add(1, shl(3, add(53, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 28 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(52, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 52 pack1 := add(1, shl(3, add(52, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 29 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(51, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 51 pack1 := add(1, shl(3, add(51, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 30 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(50, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 50 pack1 := add(1, shl(3, add(50, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 31 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(49, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 49 pack1 := add(1, shl(3, add(49, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 32 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(48, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 48 pack1 := add(1, shl(3, add(48, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 33 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(47, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 47 pack1 := add(1, shl(3, add(47, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 34 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(46, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 46 pack1 := add(1, shl(3, add(46, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 35 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(45, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 45 pack1 := add(1, shl(3, add(45, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 36 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(44, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 44 pack1 := add(1, shl(3, add(44, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 37 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(43, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 43 pack1 := add(1, shl(3, add(43, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 38 { switch item
        case 0 { meta := 15360 pack1 := add(4, shl(3, add(add(29, shl(7, 1)), shl(38, add(add(28, shl(7, add(3840, shl(30, 1)))), shl(38, add(add(25, shl(7, add(1, shl(30, 1)))), shl(38, add(24, shl(7, 3840)))))))))) pack2 := 0 pack3 := 0 }
    }
    case 39 { switch item
        case 0 { meta := add(235944960, shl(31, 1)) pack1 := add(2, shl(3, add(add(28, shl(7, add(117968640, shl(30, 1)))), shl(38, add(24, shl(7, 117968640)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(24, shl(7, 1)) pack1 := add(2, shl(3, add(add(28, shl(7, add(29491200, shl(30, 1)))), shl(38, add(24, shl(7, 14745600)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 28 pack1 := add(1, shl(3, add(28, shl(7, 14745600)))) pack2 := 0 pack3 := 0 }
    }
    case 40 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(6, shl(3, add(add(48, shl(7, 1)), shl(38, add(add(47, shl(7, 1)), shl(38, add(add(46, shl(7, 1)), shl(38, add(add(45, shl(7, 1)), shl(38, add(add(44, shl(7, 1)), shl(38, add(43, shl(7, 1)))))))))))))) pack2 := add(6, shl(3, add(add(54, shl(7, 1)), shl(38, add(add(53, shl(7, 1)), shl(38, add(add(52, shl(7, 1)), shl(38, add(add(51, shl(7, 1)), shl(38, add(add(50, shl(7, 1)), shl(38, add(49, shl(7, 1)))))))))))))) pack3 := add(6, shl(3, add(add(16, shl(7, 1)), shl(38, add(add(9, shl(7, 1)), shl(38, add(add(58, shl(7, 1)), shl(38, add(add(57, shl(7, 1)), shl(38, add(add(56, shl(7, 1)), shl(38, add(55, shl(7, 1)))))))))))))) }
        case 1 { meta := add(43, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(44, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(45, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(46, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 5 { meta := add(47, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 6 { meta := add(48, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 7 { meta := add(49, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 8 { meta := add(50, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 9 { meta := add(51, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 10 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 11 { meta := add(53, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 12 { meta := add(54, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 13 { meta := add(55, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 14 { meta := add(56, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 15 { meta := add(57, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 16 { meta := add(58, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 17 { meta := add(9, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 18 { meta := 16 pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 41 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(96, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(43, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(44, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(45, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(46, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 5 { meta := add(47, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 6 { meta := add(48, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 7 { meta := add(49, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 8 { meta := add(50, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 9 { meta := add(51, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 10 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 11 { meta := add(53, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 12 { meta := add(54, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 13 { meta := add(55, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 14 { meta := add(57, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 15 { meta := add(58, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 16 { meta := add(9, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 17 { meta := 16 pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 42 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(94, shl(7, 1)) pack1 := add(1, shl(3, add(95, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 95 pack1 := add(2, shl(3, add(add(27, shl(7, add(1, shl(30, 1)))), shl(38, add(23, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 43 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(95, shl(7, 4)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(94, shl(7, 1)) pack1 := add(1, shl(3, add(95, shl(7, add(65536, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 95 pack1 := add(2, shl(3, add(add(26, shl(7, add(1, shl(30, 1)))), shl(38, add(22, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 44 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(2, shl(3, add(add(21, shl(7, add(1, shl(30, 1)))), shl(38, add(95, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(53, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(54, shl(7, 1)) pack1 := add(1, shl(3, add(21, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := 55 pack1 := add(1, shl(3, add(21, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 45 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(62, shl(7, 1)) pack1 := add(1, shl(3, add(16, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 63 pack1 := add(1, shl(3, add(16, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 46 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(62, shl(7, 1)) pack1 := add(1, shl(3, add(16, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(63, shl(7, 1)) pack1 := add(1, shl(3, add(16, shl(7, 2)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(85, shl(7, 1)) pack1 := add(1, shl(3, add(16, shl(7, 4)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := 16 pack1 := add(1, shl(3, add(17, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 47 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(93, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 61 pack1 := add(2, shl(3, add(add(16, shl(7, add(1, shl(30, 1)))), shl(38, add(9, shl(7, add(1, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
    }
    case 48 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 61 pack1 := add(1, shl(3, add(16, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 49 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(65, shl(7, 1)) pack1 := add(1, shl(3, add(16, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 16 pack1 := add(1, shl(3, add(18, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 50 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(65, shl(7, 1)) pack1 := add(1, shl(3, add(9, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 9 pack1 := add(1, shl(3, add(11, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 51 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(64, shl(7, 1)) pack1 := add(1, shl(3, add(16, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 16 pack1 := add(1, shl(3, add(17, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 52 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(64, shl(7, 1)) pack1 := add(1, shl(3, add(9, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 9 pack1 := add(1, shl(3, add(10, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 53 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(41, shl(7, 1)) pack1 := add(2, shl(3, add(add(16, shl(7, 1)), shl(38, add(9, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(59, shl(7, 1)) pack1 := add(2, shl(3, add(add(16, shl(7, 1)), shl(38, add(9, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(60, shl(7, 1)) pack1 := add(2, shl(3, add(add(16, shl(7, add(65536, shl(30, 1)))), shl(38, add(9, shl(7, add(65536, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(3, shl(7, 1)) pack1 := add(2, shl(3, add(add(16, shl(7, 1)), shl(38, add(9, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 5 { meta := add(9, shl(7, 1)) pack1 := add(1, shl(3, add(11, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 6 { meta := 16 pack1 := add(1, shl(3, add(18, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 54 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(40, shl(7, 1)) pack1 := add(2, shl(3, add(add(16, shl(7, 1)), shl(38, add(9, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(59, shl(7, 1)) pack1 := add(2, shl(3, add(add(16, shl(7, add(65536, shl(30, 1)))), shl(38, add(9, shl(7, add(65536, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(2, shl(7, 1)) pack1 := add(2, shl(3, add(add(16, shl(7, 1)), shl(38, add(9, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(9, shl(7, 1)) pack1 := add(1, shl(3, add(10, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 5 { meta := 16 pack1 := add(1, shl(3, add(17, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 55 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(18, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 16 pack1 := add(1, shl(3, add(18, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 56 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(2, shl(3, add(add(17, shl(7, 1)), shl(38, add(39, shl(7, add(1, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(39, shl(7, 1)) pack1 := add(1, shl(3, add(16, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 16 pack1 := add(1, shl(3, add(17, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 57 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(11, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 9 pack1 := add(1, shl(3, add(11, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 58 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(2, shl(3, add(add(10, shl(7, 1)), shl(38, add(38, shl(7, add(1, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(38, shl(7, 1)) pack1 := add(1, shl(3, add(9, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 9 pack1 := add(1, shl(3, add(10, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 59 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(57, shl(7, 1)) pack1 := add(6, shl(3, add(add(76, shl(7, 256)), shl(38, add(add(75, shl(7, 1)), shl(38, add(add(72, shl(7, 256)), shl(38, add(add(71, shl(7, 1)), shl(38, add(add(68, shl(7, 256)), shl(38, add(67, shl(7, 1)))))))))))))) pack2 := add(3, shl(3, add(add(20, shl(7, add(1, shl(30, 1)))), shl(38, add(add(80, shl(7, 256)), shl(38, add(79, shl(7, 1)))))))) pack3 := 0 }
        case 2 { meta := 58 pack1 := add(3, shl(3, add(add(20, shl(7, add(1, shl(30, 1)))), shl(38, add(add(68, shl(7, 256)), shl(38, add(67, shl(7, 1)))))))) pack2 := 0 pack3 := 0 }
    }
    case 60 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(57, shl(7, 1)) pack1 := add(6, shl(3, add(add(74, shl(7, 256)), shl(38, add(add(73, shl(7, 1)), shl(38, add(add(70, shl(7, 256)), shl(38, add(add(69, shl(7, 1)), shl(38, add(add(66, shl(7, 256)), shl(38, add(65, shl(7, 1)))))))))))))) pack2 := add(3, shl(3, add(add(19, shl(7, add(1, shl(30, 1)))), shl(38, add(add(78, shl(7, 256)), shl(38, add(77, shl(7, 1)))))))) pack3 := 0 }
        case 2 { meta := 58 pack1 := add(3, shl(3, add(add(19, shl(7, add(1, shl(30, 1)))), shl(38, add(add(66, shl(7, 256)), shl(38, add(65, shl(7, 1)))))))) pack2 := 0 pack3 := 0 }
    }
    case 61 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(2, shl(3, add(add(58, shl(7, add(1, shl(30, 1)))), shl(38, add(57, shl(7, add(1, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(57, shl(7, 1)) pack1 := add(2, shl(3, add(add(58, shl(7, 2)), shl(38, add(57, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 58 pack1 := add(1, shl(3, add(58, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 62 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 92 pack1 := add(1, shl(3, add(20, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 63 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 92 pack1 := add(1, shl(3, add(19, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 64 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 91 pack1 := add(1, shl(3, add(20, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 65 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(86, shl(7, 1)) pack1 := add(1, shl(3, add(90, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 90 pack1 := add(1, shl(3, add(20, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 66 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(66, shl(7, 1)) pack1 := add(1, shl(3, add(91, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(85, shl(7, 1)) pack1 := add(1, shl(3, add(90, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(90, shl(7, 1)) pack1 := add(1, shl(3, add(19, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := 91 pack1 := add(1, shl(3, add(19, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 67 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(92, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(56, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(53, shl(7, 1)) pack1 := add(1, shl(3, add(56, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(54, shl(7, 1)) pack1 := add(1, shl(3, add(56, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := 55 pack1 := add(1, shl(3, add(56, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 68 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(2, shl(3, add(add(91, shl(7, 1)), shl(38, add(54, shl(7, add(1, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 54 pack1 := add(1, shl(3, add(56, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 69 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(3, shl(3, add(add(90, shl(7, 1)), shl(38, add(add(53, shl(7, add(1, shl(30, 1)))), shl(38, add(52, shl(7, add(1, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(56, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 53 pack1 := add(1, shl(3, add(56, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 70 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(63, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(53, shl(7, 1)) pack1 := add(1, shl(3, add(63, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := 63 pack1 := add(1, shl(3, add(89, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 71 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(41, shl(7, 1)) pack1 := add(3, shl(3, add(add(89, shl(7, 1)), shl(38, add(add(53, shl(7, 1)), shl(38, add(52, shl(7, 1)))))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(52, shl(7, 1)) pack1 := add(4, shl(3, add(add(27, shl(7, add(1, shl(30, 1)))), shl(38, add(add(23, shl(7, 1)), shl(38, add(add(62, shl(7, add(65536, shl(30, 1)))), shl(38, add(61, shl(7, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(53, shl(7, 1)) pack1 := add(4, shl(3, add(add(27, shl(7, add(1, shl(30, 1)))), shl(38, add(add(3, shl(7, 1)), shl(38, add(add(62, shl(7, add(65536, shl(30, 1)))), shl(38, add(61, shl(7, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(54, shl(7, 1)) pack1 := add(4, shl(3, add(add(27, shl(7, add(1, shl(30, 1)))), shl(38, add(add(23, shl(7, 1)), shl(38, add(add(62, shl(7, add(65536, shl(30, 1)))), shl(38, add(61, shl(7, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 5 { meta := 55 pack1 := add(4, shl(3, add(add(27, shl(7, add(1, shl(30, 1)))), shl(38, add(add(23, shl(7, 1)), shl(38, add(add(62, shl(7, add(65536, shl(30, 1)))), shl(38, add(61, shl(7, 1)))))))))) pack2 := 0 pack3 := 0 }
    }
    case 72 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(3, shl(3, add(add(89, shl(7, add(4, shl(30, 1)))), shl(38, add(add(55, shl(7, 4)), shl(38, add(54, shl(7, 4)))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(40, shl(7, 1)) pack1 := add(3, shl(3, add(add(89, shl(7, 1)), shl(38, add(add(53, shl(7, 1)), shl(38, add(52, shl(7, 1)))))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(52, shl(7, 1)) pack1 := add(3, shl(3, add(add(22, shl(7, 1)), shl(38, add(add(88, shl(7, add(1, shl(30, 1)))), shl(38, add(61, shl(7, add(65536, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(53, shl(7, 1)) pack1 := add(3, shl(3, add(add(2, shl(7, 1)), shl(38, add(add(88, shl(7, add(1, shl(30, 1)))), shl(38, add(61, shl(7, add(65536, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(54, shl(7, 1)) pack1 := add(3, shl(3, add(add(22, shl(7, 1)), shl(38, add(add(88, shl(7, add(1, shl(30, 1)))), shl(38, add(61, shl(7, add(65536, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 5 { meta := 55 pack1 := add(3, shl(3, add(add(22, shl(7, 1)), shl(38, add(add(88, shl(7, add(1, shl(30, 1)))), shl(38, add(61, shl(7, add(65536, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
    }
    case 73 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(89, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 55 pack1 := add(1, shl(3, add(66, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 74 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(41, shl(7, 1)) pack1 := add(1, shl(3, add(54, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(52, shl(7, 1)) pack1 := add(4, shl(3, add(add(23, shl(7, 1)), shl(38, add(add(86, shl(7, add(1, shl(30, 1)))), shl(38, add(add(60, shl(7, add(65536, shl(30, 1)))), shl(38, add(59, shl(7, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(53, shl(7, 1)) pack1 := add(4, shl(3, add(add(23, shl(7, 1)), shl(38, add(add(86, shl(7, add(1, shl(30, 1)))), shl(38, add(add(60, shl(7, add(65536, shl(30, 1)))), shl(38, add(59, shl(7, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(54, shl(7, 1)) pack1 := add(5, shl(3, add(add(8, shl(7, 1)), shl(38, add(add(3, shl(7, add(1, shl(30, 1)))), shl(38, add(add(86, shl(7, 1)), shl(38, add(add(60, shl(7, add(65536, shl(30, 1)))), shl(38, add(59, shl(7, 1)))))))))))) pack2 := 0 pack3 := 0 }
        case 5 { meta := 55 pack1 := add(5, shl(3, add(add(8, shl(7, 1)), shl(38, add(add(3, shl(7, add(1, shl(30, 1)))), shl(38, add(add(86, shl(7, 1)), shl(38, add(add(60, shl(7, add(65536, shl(30, 1)))), shl(38, add(59, shl(7, 1)))))))))))) pack2 := 0 pack3 := 0 }
    }
    case 75 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(2, shl(3, add(add(53, shl(7, 4)), shl(38, add(52, shl(7, 4)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(40, shl(7, 1)) pack1 := add(1, shl(3, add(54, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(52, shl(7, 1)) pack1 := add(3, shl(3, add(add(22, shl(7, 1)), shl(38, add(add(85, shl(7, add(1, shl(30, 1)))), shl(38, add(59, shl(7, add(65536, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(53, shl(7, 1)) pack1 := add(3, shl(3, add(add(22, shl(7, 1)), shl(38, add(add(85, shl(7, add(1, shl(30, 1)))), shl(38, add(59, shl(7, add(65536, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(54, shl(7, 1)) pack1 := add(4, shl(3, add(add(7, shl(7, 1)), shl(38, add(add(2, shl(7, add(1, shl(30, 1)))), shl(38, add(add(85, shl(7, 1)), shl(38, add(59, shl(7, add(65536, shl(30, 1)))))))))))) pack2 := 0 pack3 := 0 }
        case 5 { meta := 55 pack1 := add(4, shl(3, add(add(7, shl(7, 1)), shl(38, add(add(2, shl(7, add(1, shl(30, 1)))), shl(38, add(add(85, shl(7, 1)), shl(38, add(59, shl(7, add(65536, shl(30, 1)))))))))))) pack2 := 0 pack3 := 0 }
    }
    case 76 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 50 pack1 := add(1, shl(3, add(20, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 77 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 50 pack1 := add(1, shl(3, add(19, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 78 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 50 pack1 := add(1, shl(3, add(6, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 79 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 50 pack1 := add(1, shl(3, add(5, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 80 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 50 pack1 := add(1, shl(3, add(8, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 81 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 50 pack1 := add(1, shl(3, add(7, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 82 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(4, shl(3, add(add(49, shl(7, 30720)), shl(38, add(add(48, shl(7, 30720)), shl(38, add(add(47, shl(7, 30720)), shl(38, add(46, shl(7, 30720)))))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(41, shl(7, 1)) pack1 := add(2, shl(3, add(add(45, shl(7, 1)), shl(38, add(43, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(43, shl(7, 1)) pack1 := add(5, shl(3, add(add(20, shl(7, add(1, shl(30, 1)))), shl(38, add(add(8, shl(7, 1)), shl(38, add(add(3, shl(7, 1)), shl(38, add(add(60, shl(7, 1)), shl(38, add(59, shl(7, add(65536, shl(30, 1)))))))))))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(44, shl(7, 1)) pack1 := add(5, shl(3, add(add(20, shl(7, 1)), shl(38, add(add(8, shl(7, 1)), shl(38, add(add(3, shl(7, add(1, shl(30, 1)))), shl(38, add(add(60, shl(7, 1)), shl(38, add(59, shl(7, add(65536, shl(30, 1)))))))))))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(45, shl(7, 1)) pack1 := add(4, shl(3, add(add(23, shl(7, 1)), shl(38, add(add(20, shl(7, add(1, shl(30, 1)))), shl(38, add(add(60, shl(7, 1)), shl(38, add(59, shl(7, add(65536, shl(30, 1)))))))))))) pack2 := 0 pack3 := 0 }
        case 5 { meta := add(46, shl(7, 1)) pack1 := add(4, shl(3, add(add(20, shl(7, add(1, shl(30, 1)))), shl(38, add(add(86, shl(7, 1)), shl(38, add(add(60, shl(7, 1)), shl(38, add(59, shl(7, add(65536, shl(30, 1)))))))))))) pack2 := 0 pack3 := 0 }
        case 6 { meta := add(47, shl(7, 1)) pack1 := add(4, shl(3, add(add(20, shl(7, add(1, shl(30, 1)))), shl(38, add(add(86, shl(7, 1)), shl(38, add(add(60, shl(7, 1)), shl(38, add(59, shl(7, add(65536, shl(30, 1)))))))))))) pack2 := 0 pack3 := 0 }
        case 7 { meta := add(48, shl(7, 1)) pack1 := add(4, shl(3, add(add(20, shl(7, add(1, shl(30, 1)))), shl(38, add(add(86, shl(7, 1)), shl(38, add(add(60, shl(7, 1)), shl(38, add(59, shl(7, add(65536, shl(30, 1)))))))))))) pack2 := 0 pack3 := 0 }
        case 8 { meta := 49 pack1 := add(4, shl(3, add(add(20, shl(7, add(1, shl(30, 1)))), shl(38, add(add(86, shl(7, 1)), shl(38, add(add(60, shl(7, 1)), shl(38, add(59, shl(7, add(65536, shl(30, 1)))))))))))) pack2 := 0 pack3 := 0 }
    }
    case 83 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(4, shl(3, add(add(49, shl(7, 1)), shl(38, add(add(48, shl(7, 1)), shl(38, add(add(47, shl(7, 1)), shl(38, add(46, shl(7, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(40, shl(7, 1)) pack1 := add(2, shl(3, add(add(45, shl(7, 1)), shl(38, add(43, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(43, shl(7, 1)) pack1 := add(4, shl(3, add(add(19, shl(7, add(1, shl(30, 1)))), shl(38, add(add(7, shl(7, 1)), shl(38, add(add(2, shl(7, 1)), shl(38, add(60, shl(7, add(65536, shl(30, 1)))))))))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(44, shl(7, 1)) pack1 := add(4, shl(3, add(add(19, shl(7, 1)), shl(38, add(add(7, shl(7, 1)), shl(38, add(add(2, shl(7, add(1, shl(30, 1)))), shl(38, add(60, shl(7, add(65536, shl(30, 1)))))))))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(45, shl(7, 1)) pack1 := add(3, shl(3, add(add(22, shl(7, 1)), shl(38, add(add(19, shl(7, add(1, shl(30, 1)))), shl(38, add(60, shl(7, add(65536, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 5 { meta := add(46, shl(7, 1)) pack1 := add(3, shl(3, add(add(19, shl(7, add(1, shl(30, 1)))), shl(38, add(add(85, shl(7, 1)), shl(38, add(60, shl(7, add(65536, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 6 { meta := add(47, shl(7, 1)) pack1 := add(3, shl(3, add(add(19, shl(7, add(1, shl(30, 1)))), shl(38, add(add(85, shl(7, 1)), shl(38, add(60, shl(7, add(65536, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 7 { meta := add(48, shl(7, 1)) pack1 := add(3, shl(3, add(add(19, shl(7, add(1, shl(30, 1)))), shl(38, add(add(85, shl(7, 1)), shl(38, add(60, shl(7, add(65536, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 8 { meta := 49 pack1 := add(3, shl(3, add(add(19, shl(7, add(1, shl(30, 1)))), shl(38, add(add(85, shl(7, 1)), shl(38, add(60, shl(7, add(65536, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
    }
    case 84 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(4, shl(3, add(add(49, shl(7, 1)), shl(38, add(add(48, shl(7, 1)), shl(38, add(add(47, shl(7, 1)), shl(38, add(46, shl(7, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(46, shl(7, 1)) pack1 := add(1, shl(3, add(59, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(47, shl(7, 1)) pack1 := add(1, shl(3, add(59, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(48, shl(7, 1)) pack1 := add(1, shl(3, add(59, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := 49 pack1 := add(1, shl(3, add(59, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 85 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(46, shl(7, 1)) pack1 := add(6, shl(3, add(add(20, shl(7, 65536)), shl(38, add(add(19, shl(7, 1)), shl(38, add(add(8, shl(7, add(65536, shl(30, 1)))), shl(38, add(add(7, shl(7, add(1, shl(30, 1)))), shl(38, add(add(3, shl(7, add(65536, shl(30, 1)))), shl(38, add(2, shl(7, add(1, shl(30, 1)))))))))))))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(47, shl(7, 1)) pack1 := add(6, shl(3, add(add(20, shl(7, 65536)), shl(38, add(add(19, shl(7, 1)), shl(38, add(add(8, shl(7, 65536)), shl(38, add(add(7, shl(7, 1)), shl(38, add(add(3, shl(7, add(65536, shl(30, 1)))), shl(38, add(2, shl(7, add(1, shl(30, 1)))))))))))))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(48, shl(7, 1)) pack1 := add(3, shl(3, add(add(20, shl(7, 65536)), shl(38, add(add(19, shl(7, 1)), shl(38, add(87, shl(7, add(1, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := 49 pack1 := add(3, shl(3, add(add(20, shl(7, 65536)), shl(38, add(add(19, shl(7, 1)), shl(38, add(87, shl(7, add(1, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
    }
    case 86 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(87, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(49, shl(7, 1)) pack1 := add(2, shl(3, add(add(15, shl(7, 65536)), shl(38, add(14, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(2, shl(7, 1)) pack1 := add(2, shl(3, add(add(8, shl(7, add(30720, shl(30, 1)))), shl(38, add(7, shl(7, 943718400)))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := 3 pack1 := add(2, shl(3, add(add(8, shl(7, 1)), shl(38, add(7, shl(7, add(30720, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
    }
    case 87 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(21, shl(7, add(1, shl(30, 1)))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 21 pack1 := add(1, shl(3, add(21, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 88 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(22, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 0 pack1 := add(1, shl(3, add(23, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 0 pack1 := add(1, shl(3, add(4, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := 0 pack1 := add(1, shl(3, add(38, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := 0 pack1 := add(1, shl(3, add(39, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 5 { meta := 0 pack1 := add(1, shl(3, add(40, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 6 { meta := 0 pack1 := add(1, shl(3, add(41, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 7 { meta := 0 pack1 := add(1, shl(3, add(42, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 8 { meta := 0 pack1 := add(6, shl(3, add(add(48, shl(7, 32)), shl(38, add(add(47, shl(7, 16)), shl(38, add(add(46, shl(7, 8)), shl(38, add(add(45, shl(7, 4)), shl(38, add(add(44, shl(7, 2)), shl(38, add(43, shl(7, 1)))))))))))))) pack2 := add(6, shl(3, add(add(54, shl(7, 2048)), shl(38, add(add(53, shl(7, 1024)), shl(38, add(add(52, shl(7, 512)), shl(38, add(add(51, shl(7, 256)), shl(38, add(add(50, shl(7, 128)), shl(38, add(49, shl(7, 64)))))))))))))) pack3 := add(6, shl(3, add(add(16, shl(7, 131072)), shl(38, add(add(9, shl(7, 65536)), shl(38, add(add(58, shl(7, 32768)), shl(38, add(add(57, shl(7, 16384)), shl(38, add(add(56, shl(7, 8192)), shl(38, add(55, shl(7, 4096)))))))))))))) }
        case 9 { meta := 46 pack1 := 0 pack2 := 0 pack3 := 0 }
    }
    case 89 { switch item
        case 0 { meta := 524288 pack1 := add(3, shl(3, add(add(99, shl(7, add(1, shl(30, 1)))), shl(38, add(add(13, shl(7, 1)), shl(38, add(25, shl(7, add(1, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
    }
    case 90 { switch item
        case 0 { meta := 524288 pack1 := add(3, shl(3, add(add(98, shl(7, add(1, shl(30, 1)))), shl(38, add(add(6, shl(7, 1)), shl(38, add(25, shl(7, add(1, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
    }
    case 91 { switch item
        case 0 { meta := add(2, shl(30, 1)) pack1 := add(3, shl(3, add(add(99, shl(7, 524288)), shl(38, add(add(12, shl(7, 1)), shl(38, add(24, shl(7, add(1, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
    }
    case 92 { switch item
        case 0 { meta := 524288 pack1 := add(3, shl(3, add(add(97, shl(7, add(1, shl(30, 1)))), shl(38, add(add(1, shl(7, 1)), shl(38, add(25, shl(7, add(1, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
    }
    case 93 { switch item
        case 0 { meta := add(1, shl(30, 1)) pack1 := add(3, shl(3, add(add(98, shl(7, 524288)), shl(38, add(add(5, shl(7, 1)), shl(38, add(24, shl(7, add(1, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
    }
    case 94 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(29, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 95 { switch item
        case 0 { meta := 0 pack1 := add(3, shl(3, add(add(97, shl(7, 524288)), shl(38, add(add(0, shl(7, 1)), shl(38, add(24, shl(7, add(1, shl(30, 1)))))))))) pack2 := 0 pack3 := 0 }
    }
    case 96 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(18, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 97 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(26, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 98 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(11, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 99 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(17, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 100 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(88, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 101 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(10, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 102 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(20, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 103 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(23, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 104 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(86, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 105 { switch item
        case 0 { meta := 0 pack1 := add(1, shl(3, add(19, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 106 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(80, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 107 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(79, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 108 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(78, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 109 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(77, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 110 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 42 pack1 := add(1, shl(3, add(57, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 111 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(40, shl(7, 1)) pack1 := add(1, shl(3, add(57, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(57, shl(7, 1)) pack1 := add(1, shl(3, add(64, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := 58 pack1 := add(1, shl(3, add(68, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 112 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(57, shl(7, 1)) pack1 := add(2, shl(3, add(add(3, shl(7, add(7864320, shl(30, 1)))), shl(38, add(82, shl(7, 7864320)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 58 pack1 := add(3, shl(3, add(add(8, shl(7, add(7864320, shl(30, 1)))), shl(38, add(add(84, shl(7, 7864320)), shl(38, add(64, shl(7, 1)))))))) pack2 := 0 pack3 := 0 }
    }
    case 113 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(57, shl(7, 3)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 58 pack1 := add(2, shl(3, add(add(3, shl(7, add(7864320, shl(30, 1)))), shl(38, add(82, shl(7, 7864320)))))) pack2 := 0 pack3 := 0 }
    }
    case 114 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(57, shl(7, 9)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 42 pack1 := add(1, shl(3, add(58, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 115 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(76, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 116 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(75, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 117 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(74, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 118 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(73, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 119 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 42 pack1 := add(1, shl(3, add(57, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 120 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(40, shl(7, 1)) pack1 := add(1, shl(3, add(57, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(26, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(53, shl(7, 1)) pack1 := add(1, shl(3, add(26, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(54, shl(7, 1)) pack1 := add(1, shl(3, add(26, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 5 { meta := add(55, shl(7, 1)) pack1 := add(1, shl(3, add(26, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 6 { meta := add(57, shl(7, 1)) pack1 := add(1, shl(3, add(64, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 7 { meta := 58 pack1 := add(1, shl(3, add(67, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 121 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(63, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(53, shl(7, 1)) pack1 := add(1, shl(3, add(63, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(54, shl(7, 1)) pack1 := add(1, shl(3, add(63, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(55, shl(7, 1)) pack1 := add(1, shl(3, add(63, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 5 { meta := add(57, shl(7, 1)) pack1 := add(1, shl(3, add(82, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 6 { meta := 58 pack1 := add(2, shl(3, add(add(84, shl(7, 1)), shl(38, add(64, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
    }
    case 122 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(57, shl(7, 2)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(88, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(53, shl(7, 1)) pack1 := add(1, shl(3, add(88, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(54, shl(7, 1)) pack1 := add(1, shl(3, add(88, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(55, shl(7, 1)) pack1 := add(1, shl(3, add(88, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 5 { meta := 58 pack1 := add(1, shl(3, add(82, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 123 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(5, shl(3, add(add(57, shl(7, 9)), shl(38, add(add(55, shl(7, 2)), shl(38, add(add(54, shl(7, 2)), shl(38, add(add(53, shl(7, 2)), shl(38, add(52, shl(7, 2)))))))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 42 pack1 := add(1, shl(3, add(58, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 124 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(72, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 125 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(71, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 126 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(70, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 127 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(69, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 128 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 42 pack1 := add(1, shl(3, add(57, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 129 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(40, shl(7, 1)) pack1 := add(1, shl(3, add(57, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(57, shl(7, 1)) pack1 := add(1, shl(3, add(64, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := 58 pack1 := add(1, shl(3, add(66, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 130 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(41, shl(7, 1)) pack1 := add(1, shl(3, add(58, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(66, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(53, shl(7, 1)) pack1 := add(1, shl(3, add(66, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(54, shl(7, 1)) pack1 := add(1, shl(3, add(66, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 5 { meta := add(55, shl(7, 1)) pack1 := add(1, shl(3, add(66, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 6 { meta := add(57, shl(7, 1)) pack1 := add(2, shl(3, add(add(2, shl(7, add(7864320, shl(30, 1)))), shl(38, add(81, shl(7, 7864320)))))) pack2 := 0 pack3 := 0 }
        case 7 { meta := 58 pack1 := add(2, shl(3, add(add(7, shl(7, add(7864320, shl(30, 1)))), shl(38, add(83, shl(7, 7864320)))))) pack2 := 0 pack3 := 0 }
    }
    case 131 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(1, shl(3, add(57, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(42, shl(7, 1)) pack1 := add(4, shl(3, add(add(55, shl(7, 524288)), shl(38, add(add(54, shl(7, 524288)), shl(38, add(add(53, shl(7, 524288)), shl(38, add(52, shl(7, 524288)))))))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(52, shl(7, 1)) pack1 := add(4, shl(3, add(add(8, shl(7, 1)), shl(38, add(add(65, shl(7, 65536)), shl(38, add(add(64, shl(7, 262144)), shl(38, add(60, shl(7, 131072)))))))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(53, shl(7, 1)) pack1 := add(4, shl(3, add(add(8, shl(7, 1)), shl(38, add(add(65, shl(7, 65536)), shl(38, add(add(64, shl(7, 262144)), shl(38, add(60, shl(7, 131072)))))))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(54, shl(7, 1)) pack1 := add(4, shl(3, add(add(8, shl(7, 1)), shl(38, add(add(65, shl(7, 65536)), shl(38, add(add(64, shl(7, 262144)), shl(38, add(60, shl(7, 131072)))))))))) pack2 := 0 pack3 := 0 }
        case 5 { meta := add(55, shl(7, 1)) pack1 := add(4, shl(3, add(add(8, shl(7, 1)), shl(38, add(add(65, shl(7, 65536)), shl(38, add(add(64, shl(7, 262144)), shl(38, add(60, shl(7, 131072)))))))))) pack2 := 0 pack3 := 0 }
        case 6 { meta := 58 pack1 := add(2, shl(3, add(add(2, shl(7, add(7864320, shl(30, 1)))), shl(38, add(81, shl(7, 7864320)))))) pack2 := 0 pack3 := 0 }
    }
    case 132 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(5, shl(3, add(add(57, shl(7, 9)), shl(38, add(add(55, shl(7, 31)), shl(38, add(add(54, shl(7, 31)), shl(38, add(add(53, shl(7, 31)), shl(38, add(52, shl(7, 31)))))))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 42 pack1 := add(1, shl(3, add(58, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 133 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(68, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 134 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(67, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 135 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(66, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 136 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 57 pack1 := add(1, shl(3, add(65, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 137 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := 42 pack1 := add(1, shl(3, add(57, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 138 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(40, shl(7, 1)) pack1 := add(1, shl(3, add(57, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(57, shl(7, 1)) pack1 := add(1, shl(3, add(64, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := 58 pack1 := add(1, shl(3, add(65, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 139 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(40, shl(7, 1)) pack1 := add(1, shl(3, add(58, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(65, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(53, shl(7, 1)) pack1 := add(1, shl(3, add(65, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(54, shl(7, 1)) pack1 := add(1, shl(3, add(65, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 5 { meta := add(55, shl(7, 1)) pack1 := add(1, shl(3, add(65, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 6 { meta := add(57, shl(7, 1)) pack1 := add(1, shl(3, add(81, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 7 { meta := 58 pack1 := add(1, shl(3, add(83, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 140 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(3, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(53, shl(7, 1)) pack1 := add(1, shl(3, add(3, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(54, shl(7, 1)) pack1 := add(1, shl(3, add(3, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(55, shl(7, 1)) pack1 := add(1, shl(3, add(3, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 5 { meta := 58 pack1 := add(1, shl(3, add(81, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 141 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(5, shl(3, add(add(57, shl(7, 9)), shl(38, add(add(55, shl(7, 5)), shl(38, add(add(54, shl(7, 5)), shl(38, add(add(53, shl(7, 5)), shl(38, add(52, shl(7, 5)))))))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 42 pack1 := add(1, shl(3, add(58, shl(7, 1)))) pack2 := 0 pack3 := 0 }
    }
    case 142 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(57, shl(7, 1)) pack1 := add(1, shl(3, add(64, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(8, shl(7, 1)) pack1 := add(1, shl(3, add(93, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(9, shl(7, 1)) pack1 := add(2, shl(3, add(add(20, shl(7, 1)), shl(38, add(8, shl(7, add(1, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := 16 pack1 := add(2, shl(3, add(add(20, shl(7, 1)), shl(38, add(8, shl(7, add(1, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
    }
    case 143 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(52, shl(7, 1)) pack1 := add(1, shl(3, add(64, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(53, shl(7, 1)) pack1 := add(1, shl(3, add(64, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(54, shl(7, 1)) pack1 := add(1, shl(3, add(64, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(55, shl(7, 1)) pack1 := add(1, shl(3, add(64, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 5 { meta := add(57, shl(7, 1)) pack1 := add(2, shl(3, add(add(7, shl(7, add(7864320, shl(30, 1)))), shl(38, add(83, shl(7, 7864320)))))) pack2 := 0 pack3 := 0 }
        case 6 { meta := add(58, shl(7, 1)) pack1 := add(1, shl(3, add(64, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 7 { meta := add(7, shl(7, 1)) pack1 := add(1, shl(3, add(93, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 8 { meta := add(9, shl(7, 1)) pack1 := add(2, shl(3, add(add(19, shl(7, 1)), shl(38, add(7, shl(7, add(1, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
        case 9 { meta := 16 pack1 := add(2, shl(3, add(add(19, shl(7, 1)), shl(38, add(7, shl(7, add(1, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
    }
    case 144 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := 0 pack2 := 0 pack3 := 0 }
        case 1 { meta := add(41, shl(7, 1)) pack1 := add(1, shl(3, add(58, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 2 { meta := add(52, shl(7, 1)) pack1 := add(2, shl(3, add(add(86, shl(7, 1)), shl(38, add(85, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 3 { meta := add(53, shl(7, 1)) pack1 := add(2, shl(3, add(add(86, shl(7, 1)), shl(38, add(85, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 4 { meta := add(54, shl(7, 1)) pack1 := add(2, shl(3, add(add(86, shl(7, 1)), shl(38, add(85, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 5 { meta := add(55, shl(7, 1)) pack1 := add(2, shl(3, add(add(86, shl(7, 1)), shl(38, add(85, shl(7, 1)))))) pack2 := 0 pack3 := 0 }
        case 6 { meta := add(57, shl(7, 1)) pack1 := add(1, shl(3, add(83, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 7 { meta := add(64, shl(7, 1)) pack1 := add(1, shl(3, add(93, shl(7, 1)))) pack2 := 0 pack3 := 0 }
        case 8 { meta := 65 pack1 := add(1, shl(3, add(93, shl(7, 65536)))) pack2 := 0 pack3 := 0 }
    }
    case 145 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(6, shl(3, add(add(58, shl(7, 3)), shl(38, add(add(57, shl(7, 8)), shl(38, add(add(55, shl(7, 1)), shl(38, add(add(54, shl(7, 1)), shl(38, add(add(53, shl(7, 1)), shl(38, add(52, shl(7, 1)))))))))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := 21 pack1 := add(1, shl(3, add(93, shl(7, 34)))) pack2 := 0 pack3 := 0 }
    }
    case 146 { switch item
        case 0 { meta := add(0, shl(31, 1)) pack1 := add(2, shl(3, add(add(16, shl(7, add(64, shl(30, 1)))), shl(38, add(9, shl(7, add(64, shl(30, 1)))))))) pack2 := 0 pack3 := 0 }
        case 1 { meta := add(9, shl(7, 1)) pack1 := add(2, shl(3, add(add(65, shl(7, 1)), shl(38, add(61, shl(7, 65536)))))) pack2 := 0 pack3 := 0 }
        case 2 { meta := 16 pack1 := add(2, shl(3, add(add(65, shl(7, 1)), shl(38, add(61, shl(7, 65536)))))) pack2 := 0 pack3 := 0 }
    }
}
// memory related
function memrel_to_calldata(addr_space, addr_low, addr_high, ts_low, ts_high, val_low, val_high) -> compressed {
    compressed := add(memory_gamma(), addr_space)
    compressed := add(compressed, mulmod(memory_alpha1(), addr_low, P))
    compressed := add(compressed, mulmod(memory_alpha2(), addr_high, P))
    compressed := add(compressed, mulmod(memory_alpha3(), ts_low, P))
    compressed := add(compressed, mulmod(memory_alpha4(), ts_high, P))
    compressed := add(compressed, mulmod(memory_alpha5(), val_low, P))
    compressed := add(compressed, mulmod(memory_alpha6(), val_high, P))
}
function memrelinitpart_to_calldata(ts_low, ts_high, val_low, val_high) -> compressed {
    compressed := add(compressed, mulmod(memory_alpha3(), ts_low, P))
    compressed := add(compressed, mulmod(memory_alpha4(), ts_high, P))
    compressed := add(compressed, mulmod(memory_alpha5(), val_low, P))
    compressed := add(compressed, mulmod(memory_alpha6(), val_high, P))
}
function memrel_from_pack(ptr, pack) -> value {
    let addr_space := and(pack, sub(shl(9, 1), 1)) // 9 bits
    pack := shr(9, pack)
    {
        let is_var := and(addr_space, 1)
        addr_space := shr(1, addr_space)
        if is_var {
            let var_idx := and(addr_space, sub(shl(7, 1), 1)) // 7 bits
            let var := gate_calldataload(ptr, var_idx)
            let is_neg_var := shr(7, addr_space)
            if is_neg_var {
                var := add(1, u128_neg(var))
            }
            addr_space := var
        }
    }

    let addr_low := and(pack, sub(shl(17, 1), 1)) // 17 bits
    let addr_high
    pack := shr(17, pack)
    {
        let is_var_low := and(addr_low, 1)
        addr_low := shr(1, addr_low)
        if is_var_low {
            let var_low_idx := and(addr_low, sub(shl(7, 1), 1)) // 7 bits
            let var_low := gate_calldataload(ptr, var_low_idx)
            let is_var_high := shr(7, addr_low)
            if is_var_high {
                let var_high_idx := shr(1, is_var_high)
                let var_high := gate_calldataload(ptr, var_high_idx)
                addr_high := var_high
            }
            addr_low := var_low
        }
    }

    let ts_low := and(pack, sub(shl(17, 1), 1)) // 17 bits
    let ts_high
    pack := shr(17, pack)
    {
        let is_vars := ts_low
        ts_low := shr(1, ts_low)
        if is_vars {
            let offset := and(ts_low, 3) // 2 bits
            let vars_idx := shr(2, ts_low) // 7+7 bits
            let var_low_idx := and(vars_idx, sub(shl(7, 1), 1)) // 7 bits
            let var_high_idx := shr(7, vars_idx) // 7 bits
            let var_low := gate_calldataload(ptr, var_low_idx)
            let var_high := gate_calldataload(ptr, var_high_idx)
            ts_low := add(var_low, offset)
            ts_high := var_high
        }
    }

    let val_low := and(pack, sub(shl(30, 1), 1)) // 30 bits
    let val_high
    pack := shr(30, pack)
    {
        let is_vars := val_low
        val_low := shr(1, val_low)
        if is_vars {
            let is_vars_u8 := and(val_low, 1)
            val_low := shr(1, val_low)
            let var_low_idx := and(val_low, sub(shl(7, 1), 1)) // 7 bits
            let var_high_idx := and(shr(7, val_low), sub(shl(7, 1), 1)) // 7 bits
            let var_low := gate_calldataload(ptr, var_low_idx)
            let var_high := gate_calldataload(ptr, var_high_idx)
            if is_vars_u8 {
                let var_lh_idx := and(shr(14, val_low), sub(shl(7, 1), 1)) // 7 bits
                let var_hh_idx := shr(21, val_low) // 7 bits
                let var_lh := gate_calldataload(ptr, var_lh_idx)
                let var_hh := gate_calldataload(ptr, var_hh_idx)
                var_low := add(var_low, shl(8, var_lh))
                var_high := add(var_high, shl(8, var_hh))
            }
            val_low := var_low
            val_high := var_high
        }
    }

    value := memrel_to_calldata(addr_space, addr_low, addr_high, ts_low, ts_high, val_low, val_high)
}
function memrelinitpart_from_pack(ptr, pack) -> value {
    let ts_low := pack // 29 bits
    let ts_high, val_low, val_high
    {
        let is_vars := ts_low
        ts_low := shr(1, ts_low)
        if is_vars {
            let ts_low_idx := and(ts_low, sub(shl(7, 1), 1)) // 7 bits
            let ts_high_idx := and(shr(7, ts_low), sub(shl(7, 1), 1)) // 7 bits
            let val_low_idx := and(shr(14, ts_low), sub(shl(7, 1), 1)) // 7 bits
            let val_high_idx := shr(21, ts_low) // 7 bits
            ts_low := gate_calldataload(ptr, ts_low_idx)
            ts_high := gate_calldataload(ptr, ts_high_idx)
            val_low := gate_calldataload(ptr, val_low_idx)
            val_high := gate_calldataload(ptr, val_high_idx)
        }
    }
    value := memrelinitpart_to_calldata(ts_low, ts_high, val_low, val_high)
}


// 3
function gate_aggregatelookuprationalpair(ptr, alpha, acc, num1_idx, num2_idx, den1_idx, den2_idx) -> next_acc {
    let num1 := gate_calldataload(ptr, num1_idx)
    let num2 := gate_calldataload(ptr, num2_idx)
    let den1 := gate_calldataload(ptr, den1_idx)
    let den2 := gate_calldataload(ptr, den2_idx)
    let den_out := mulmod(den1, den2, P)
    let num_out := add(mulmod(num1, den2, P), mulmod(num2, den1, P))
    next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
}
function gate_copyinextensionfield(ptr, alpha, acc, input_idx) -> next_acc {
    let input := gate_calldataload(ptr, input_idx)
    next_acc := pointcheck_update(acc, alpha, input)
}

// 2
function gate_maskintoidentityproduct(ptr, alpha, acc, input_idx, mask_idx) -> next_acc {
    let input := gate_calldataload(ptr, input_idx)
    let mask := gate_calldataload(ptr, mask_idx)
    // let neg_mask := u128_neg(mask)
    // let gate := add(mulmod(input, mask, P), add(1, neg_mask))
    let neg_one := sub(P, 1)
    let gate := add(mulmod(mask, add(input, neg_one), P), 1)
    next_acc := pointcheck_update(acc, alpha, gate)
}

// 1
function gate_copyinbasefield(ptr, alpha, acc, input_idx) -> next_acc {
    let input := gate_calldataload(ptr, input_idx)
    next_acc := pointcheck_update(acc, alpha, input)
}
function gate_trivialproduct(ptr, alpha, acc, lhs_idx, rhs_idx) -> next_acc {
    let lhs := gate_calldataload(ptr, lhs_idx)
    let rhs := gate_calldataload(ptr, rhs_idx)
    let gate := mulmod(lhs, rhs, P)
    next_acc := pointcheck_update(acc, alpha, gate)
}
function gate_lookupunbalancedpairwithmaterializedbaseinputs(ptr, alpha, acc, num1_idx, den1_idx, den2_remainder_idx) -> next_acc {
    let num1 := gate_calldataload(ptr, num1_idx)
    let den1 := gate_calldataload(ptr, den1_idx)
    let den2_remainder := gate_calldataload(ptr, den2_remainder_idx)
    let den2 := add(logup_gamma(), den2_remainder)
    let den_out := mulmod(den1, den2, P)
    let num_out := add(mulmod(num1, den2, P), den1)
    next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
}
// (unified)
function gate_lookuppairfromvectorinputs(ptr, alpha, acc, den1_cfg, den2_cfg) -> next_acc {
    let den1 := lookrelgeneric_from_cfg(ptr, den1_cfg)
    let den2 := lookrelgeneric_from_cfg(ptr, den2_cfg)
    let den_out := mulmod(den1, den2, P)
    let num_out := add(den2, den1)
    next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
}
function gate_lookupunbalancedpairwithvectorinputs(ptr, alpha, acc, num1_idx, den1_idx, den2_cfg) -> next_acc {
    let num1 := gate_calldataload(ptr, num1_idx)
    let den1 := gate_calldataload(ptr, den1_idx)
    let den2 := lookrelgeneric_from_cfg(ptr, den2_cfg)
    let den_out := mulmod(den1, den2, P)
    let num_out := add(mulmod(num1, den2, P), den1)
    next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
}

// 0
function gate_initialgrandproductwithoutcaches(ptr, alpha, acc, lhs_pack, rhs_pack) -> next_acc {
    let lhs := memrel_from_pack(ptr, lhs_pack)
    let rhs := memrel_from_pack(ptr, rhs_pack)
    let gate := mulmod(lhs, rhs, P)
    next_acc := pointcheck_update(acc, alpha, gate)
}
function gate_lookupfrommaterializedbaseinputwithsetup(ptr, alpha, acc, num2_idx, den1_remainder_idx, den2_remainder_cacheidx) -> next_acc {
    let num2 := gate_calldataload(ptr, num2_idx)
    let den1_remainder := gate_calldataload(ptr, den1_remainder_idx)
    let den2_remainder := gate_mload(ptr, den2_remainder_cacheidx)
    let den1 := add(logup_gamma(), den1_remainder)
    let den2 := add(logup_gamma(), den2_remainder)
    let den_out := mulmod(den1, den2, P)
    let num_out := add(den2, sub(P, mulmod(num2, den1, P)))
    next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
}
function gate_lookuppairfrombaseinputs(ptr, alpha, acc, den1_cfg, den2_cfg) -> next_acc {
    let den1 := lookrelsingle_from_cfg(ptr, den1_cfg)
    let den2 := lookrelsingle_from_cfg(ptr, den2_cfg)
    let den_out := mulmod(den1, den2, P)
    let num_out := add(den2, den1)
    next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
}
function gate_materializesinglelookupinput(ptr, alpha, acc, compressed_tuple_cfg) -> next_acc {
    let compressed_tuple := linrel_from_cfg(ptr, compressed_tuple_cfg)
    next_acc := pointcheck_update(acc, alpha, compressed_tuple)
}
function gate_lookupwithdensandsetupexpressions(ptr, alpha, acc, num1_idx, num2_idx, den1_cfg, den2_remainder_pack) -> next_acc {
    let num1 := gate_calldataload(ptr, num1_idx)
    let num2 := gate_calldataload(ptr, num2_idx)
    let den1 := lookrelgeneric_from_cfg(ptr, den1_cfg)
    let den2_remainder
    for { let i := 0 } lt(i, 10) { i := add(i, 1) } {
        let idx := and(den2_remainder_pack, sub(shl(7, 1), 1)) // 7 bits
        let var := gate_calldataload(ptr, idx)
        den2_remainder := add(mulmod(den2_remainder, logup_alpha(), P), var)
        den2_remainder_pack := shr(7, den2_remainder_pack)
    }
    let den2 := add(logup_gamma(), den2_remainder)
    let den_out := mulmod(den1, den2, P)
    let num_out := add(mulmod(num1, den2, P), sub(P, mulmod(num2, den1, P)))
    next_acc := logup_pointcheck_update(acc, alpha, num_out, den_out)
}
function gate_enforcesinglemaxquadraticconstraint(ptr, alpha, acc, input_cfg) -> next_acc {
    let input := quadrel_from_cfg(ptr, input_cfg)
    next_acc := add(mulmod(acc, alpha, P), input)
}
// (unified)
function gate_initsorteardownsinitialpair(ptr, alpha, acc, addr_low_cacheidx, addr_high_base_cacheidx, addr_high_tops_pack, lhs_ts_and_val_pack, rhs_ts_and_val_pack) -> next_acc {
    let addr_low := gate_mload(ptr, addr_low_cacheidx)
    let addr_high_base := gate_mload(ptr, addr_high_base_cacheidx)
    let lhs_addr_high_top := and(addr_high_tops_pack, sub(shl(8, 1), 1)) // 8 bits
    let rhs_addr_high_top := shr(8, addr_high_tops_pack) // 8 bits
    let shared := add(add(memory_gamma(), 1), mulmod(memory_alpha1(), addr_low, P))
    let lhs_addr_high := add(addr_high_base, shl(10, lhs_addr_high_top))
    let rhs_addr_high := add(addr_high_base, shl(10, rhs_addr_high_top))
    let lhs_upper := memrelinitpart_from_pack(ptr, lhs_ts_and_val_pack)
    let rhs_upper := memrelinitpart_from_pack(ptr, rhs_ts_and_val_pack)
    let lhs := add(shared, add(mulmod(memory_alpha2(), lhs_addr_high, P), lhs_upper))
    let rhs := add(shared, add(mulmod(memory_alpha2(), rhs_addr_high, P), rhs_upper))
    let gate := mulmod(lhs, rhs, P)
    next_acc := pointcheck_update(acc, alpha, gate)
}
function gate_maxquadratic(ptr, alpha, acc, input_cfg) -> next_acc {
    let input := quadrel_from_cfg(ptr, input_cfg)
    next_acc := add(mulmod(acc, alpha, P), input)
}


