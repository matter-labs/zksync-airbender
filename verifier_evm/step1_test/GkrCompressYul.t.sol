// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseBytes(string calldata s) external pure returns (bytes memory);
}

/// Validates gkr_compress Yul (18 dim-reducing layers) against the Rust mirror's
/// post-dim-reducing state: seed 0xc3616d7d…, batching 0x06616d7d…, point = 22 coords.
/// Pipeline: transcript_init -> gkr_init -> gkr_compress on the REAL calldata
/// (preimage || outputEvals || dim-reduce blob), read via calldataload like gkr.sol.
///   forge test --match-contract GkrCompressYulTest -vv
contract GkrCompressYulTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    function _rd(string memory p) internal view returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", vm.readFile(p)));
    }

    function test_gkr_compress_matches_mirror() external {
        bytes memory pre = _rd("../whir/testdata/gkr_step1_preimage.hex");
        bytes memory outs = _rd("../whir/testdata/gkr_step2_output_evals.hex");
        bytes memory blob = _rd("../whir/testdata/gkr_dimreduce_data.hex");
        (bytes32 seedOut, uint256 batchingOut, uint256 failCode) = this.run(bytes.concat(pre, outs, blob));
        emit log_named_uint("failCode(k*65536 + type*256 + round)", failCode);
        require(failCode == 0, "a layer check failed");

        require(batchingOut == 0x06616d7d0fe9664e9ad006cc97f250ae, "batching mismatch");
        require(
            seedOut == 0xc3616d7d0fe9664e9ad006cc97f250c978fde8d241a2d9d467b73925d8c28fe0,
            "seed mismatch"
        );
    }

    event log_named_uint(string k, uint256 v);
    function run(bytes calldata cd) external pure returns (bytes32 seedOut, uint256 batchingOut, uint256 failCode) {
        assembly {
            let P := 0x7000000000000000000000000000001
            let MASK := 0xffffffffffffffffffffffffffffffff
            let base := cd.offset // calldata offset of the stream
            // scratch memory (free region)
            let SD := mload(0x40)
            let PT := add(SD, 64)             // point (22 slots)
            let CL := add(PT, mul(32, 24))    // claims (10 slots)
            let EQ := add(CL, mul(32, 12))    // eq[16]
            let SI := add(EQ, mul(32, 18))    // sorted-index scratch (10)
            let ABS := add(SI, mul(32, 12))   // absorb scratch (seed + up to 2560)

            // ---- transcript_init (validated) ----
            let seed := keccak256(0, 0) // placeholder to declare
            calldatacopy(ABS, base, 520)
            seed := keccak256(ABS, 520)
            mstore(ABS, seed) mstore(add(ABS, 32), 0)
            seed := keccak256(ABS, 40)
            mstore(ABS, seed)
            for { let i := 0 } lt(i, 9) { i := add(i, 1) } { seed := keccak256(ABS, 32) mstore(ABS, seed) }

            // ---- gkr_init (validated): absorb outputs, draw eval_point[4]+batching, 10 claims ----
            let ob := add(base, 520) // outputEvals calldata offset
            mstore(ABS, seed)
            calldatacopy(add(ABS, 32), ob, 2560)
            seed := keccak256(ABS, 2592)
            mstore(ABS, seed)
            for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                seed := keccak256(ABS, 32) mstore(ABS, seed)
                mstore(add(PT, mul(i, 32)), mod(shr(128, seed), P))
            }
            seed := keccak256(ABS, 32) mstore(ABS, seed)
            let batching := mod(shr(128, seed), P)
            for { let j := 0 } lt(j, 16) { j := add(j, 1) } {
                let e := 1
                for { let v := 0 } lt(v, 4) { v := add(v, 1) } {
                    let zv := mload(add(PT, mul(v, 32)))
                    let f := zv
                    if iszero(and(shr(sub(3, v), j), 1)) { f := add(1, sub(P, zv)) }
                    e := mulmod(e, f, P)
                }
                mstore(add(EQ, mul(j, 32)), e)
            }
            for { let c := 0 } lt(c, 10) { c := add(c, 1) } {
                let acc := 0
                for { let j := 0 } lt(j, 16) { j := add(j, 1) } {
                    let val := shr(128, calldataload(add(ob, mul(add(mul(c, 16), j), 16))))
                    acc := add(mulmod(val, mload(add(EQ, mul(j, 32))), P), acc)
                }
                mstore(add(CL, mul(c, 32)), mod(acc, P))
            }

            // ---- gkr_compress: 18 dim-reducing layers ----
            let ptr := add(ob, 2560) // dim-reduce blob calldata offset
            for { let k := 0 } lt(k, 18) { k := add(k, 1) } {
                let fs := add(4, k)
                let claim := 0
                let cb := 1
                for { let c := 0 } lt(c, 10) { c := add(c, 1) } {
                    claim := add(mulmod(cb, mload(add(CL, mul(c, 32))), P), claim)
                    cb := mulmod(cb, batching, P)
                }
                claim := mod(claim, P)
                // sumcheck rounds
                let eq_scale := 1
                for { let i := 0 } lt(i, fs) { i := add(i, 1) } {
                    let w0 := calldataload(ptr)
                    let w1 := calldataload(add(ptr, 32))
                    let c0 := shr(128, w0)
                    let c1 := and(w0, MASK)
                    let c2 := shr(128, w1)
                    let c3 := and(w1, MASK)
                    let sum01 := mulmod(add(add(add(add(c0, c0), c1), c2), c3), eq_scale, P)
                    if mod(add(claim, sub(P, mod(sum01, P))), P) { if iszero(failCode) { failCode := add(add(mul(k, 65536), 256), i) } }
                    mstore(ABS, seed) mstore(add(ABS, 32), w0) mstore(add(ABS, 64), w1)
                    seed := keccak256(ABS, 96) mstore(ABS, seed) // absorb
                    seed := keccak256(ABS, 32) mstore(ABS, seed) // draw
                    let r := mod(shr(128, seed), P)
                    claim := add(mulmod(add(mulmod(add(mulmod(c3, r, P), c2), r, P), c1), r, P), c0)
                    let z := mload(add(PT, mul(i, 32)))
                    eq_scale := add(add(add(mulmod(z, r, P), mulmod(z, r, P)), 1), sub(mul(4, P), add(z, r)))
                    mstore(add(PT, mul(i, 32)), r)
                    ptr := add(ptr, 64)
                }
                // final step: sorted-index per logical slot (perm on the last/boundary layer)
                for { let li := 0 } lt(li, 10) { li := add(li, 1) } { mstore(add(SI, mul(li, 32)), li) }
                if eq(k, 17) {
                    mstore(add(SI, 0), 6) mstore(add(SI, 32), 7)
                    mstore(add(SI, 64), 0) mstore(add(SI, 96), 1) mstore(add(SI, 128), 2)
                    mstore(add(SI, 160), 3) mstore(add(SI, 192), 4) mstore(add(SI, 224), 5)
                    mstore(add(SI, 256), 8) mstore(add(SI, 288), 9)
                }
                let g := 0
                let gb := 1
                for { let step := 0 } lt(step, 2) { step := add(step, 1) } {
                    let word := calldataload(add(ptr, mul(mload(add(SI, mul(step, 32))), 32)))
                    g := add(mulmod(gb, mulmod(shr(128, word), and(word, MASK), P), P), g)
                    gb := mulmod(gb, batching, P)
                }
                for { let pr := 0 } lt(pr, 3) { pr := add(pr, 1) } {
                    let wN := calldataload(add(ptr, mul(mload(add(SI, mul(add(2, mul(pr, 2)), 32))), 32)))
                    let wD := calldataload(add(ptr, mul(mload(add(SI, mul(add(3, mul(pr, 2)), 32))), 32)))
                    let num := add(mulmod(shr(128, wN), and(wD, MASK), P), mulmod(and(wN, MASK), shr(128, wD), P))
                    let den := mulmod(shr(128, wD), and(wD, MASK), P)
                    g := add(mulmod(gb, num, P), g) gb := mulmod(gb, batching, P)
                    g := add(mulmod(gb, den, P), g) gb := mulmod(gb, batching, P)
                }
                for { let step := 8 } lt(step, 10) { step := add(step, 1) } {
                    let word := calldataload(add(ptr, mul(mload(add(SI, mul(step, 32))), 32)))
                    g := add(mulmod(gb, mulmod(shr(128, word), and(word, MASK), P), P), g)
                    gb := mulmod(gb, batching, P)
                }
                if mod(add(mulmod(mod(g, P), eq_scale, P), sub(P, claim)), P) { if iszero(failCode) { failCode := add(mul(k, 65536), 512) } }
                // absorb LSB (320 B, sorted), draw r_last + next_batching
                mstore(ABS, seed)
                calldatacopy(add(ABS, 32), ptr, 320)
                seed := keccak256(ABS, 352) mstore(ABS, seed)
                seed := keccak256(ABS, 32) mstore(ABS, seed)
                let r_last := mod(shr(128, seed), P)
                seed := keccak256(ABS, 32) mstore(ABS, seed)
                let next_batching := mod(shr(128, seed), P)
                mstore(add(PT, mul(fs, 32)), r_last)
                // next claims = interpolate lsb_sorted at r_last (SORTED, no perm)
                for { let li := 0 } lt(li, 10) { li := add(li, 1) } {
                    let word := calldataload(add(ptr, mul(li, 32)))
                    let a := shr(128, word)
                    let b := and(word, MASK)
                    // a + (b-a)*r_last
                    mstore(add(CL, mul(li, 32)), add(a, mulmod(add(b, sub(P, a)), r_last, P)))
                }
                batching := next_batching
                ptr := add(ptr, 320)
            }
            seedOut := seed
            batchingOut := batching
        }
    }
}
