// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// STEP 2b of the production GKR verifier: the dimension-reducing layers.
///
/// Circuit-AGNOSTIC except for one code-gen constant (`_BOUNDARY_PERM`), which encodes
/// the circuit's `global_output_map` ordering for the boundary layer (the one whose
/// inputs are the circuit outputs). Everything else is fixed.
///
/// Layers are processed OUTPUT->base: folding_steps = 4,5,...,21 (18 layers here). Each
/// layer:
///   1. initial claim = RLC(prev at-point claims, running `batching` powers)
///   2. `folding_steps` monomial sumcheck rounds p(X)=c0+c1X+c2X^2+c3X^3:
///        check claim == (2c0+c1+c2+c3)*eq_prefactor; absorb 4 coeffs; draw r;
///        claim = p(r); eq_prefactor = (1-r)(1-point[round]) + r*point[round].
///   3. final-step: 10 LSB lines ([E;2] each). Accumulate g (products for slots 0,1,8,9;
///        lookup num/den for pairs (2,3),(4,5),(6,7)) with `batching` powers; check
///        g*eq_prefactor == claim. Absorb LSB lines (SORTED order); draw [r_last,next_batching].
///        next claims = LSB interpolated at r_last; batching = next_batching.
///
/// All field elements are Proth120 (extension degree 1) => scalar arithmetic mod P.
contract GkrDimReduce {
    uint256 constant P = 0x7000000000000000000000000000001;

    // Boundary-layer permutation: lsb_logical[i] = lsb_sorted[_BOUNDARY_PERM[i]].
    // Derived from `unified_circuit.global_output_map` (code-gen):
    //   PermProduct@{6,7}, Lookup16@{0,1}, LookupTs@{2,3}, Generic@{4,5}, Inits@{8,9}.
    function _boundaryPerm() internal pure returns (uint256[10] memory) {
        return [uint256(6), 7, 0, 1, 2, 3, 4, 5, 8, 9];
    }

    struct St {
        bytes32 seed;
        uint256 batching;
        uint256[] point;
        uint256[] claims;
        uint256 off; // byte offset into blob
    }

    function verifyDimReduce(
        bytes calldata preimage,
        uint64 nonce,
        uint32 powBits,
        bytes calldata outputEvals,
        uint256 numEvalPointCoords,
        bytes calldata blob
    ) external pure returns (bytes32 seedOut, uint256 batchingOut, uint256 pointLen) {
        St memory s;

        // ---- entry (STEP 1 skip + STEP 2a) ----
        bytes32 seed = keccak256(preimage);
        seed = keccak256(abi.encodePacked(seed, nonce));
        if (powBits > 0) {
            require(uint256(seed) >> (256 - uint256(powBits)) == 0, "pow bits nonzero");
        }
        for (uint256 i = 0; i < 9; i++) {
            seed = keccak256(abi.encodePacked(seed));
        }
        seed = keccak256(abi.encodePacked(seed, outputEvals));

        s.point = new uint256[](numEvalPointCoords);
        for (uint256 i = 0; i < numEvalPointCoords; i++) {
            seed = keccak256(abi.encodePacked(seed));
            s.point[i] = (uint256(seed) >> 128) % P;
        }
        seed = keccak256(abi.encodePacked(seed));
        s.batching = (uint256(seed) >> 128) % P;
        s.seed = seed;

        // ---- initial 10 claims = each output column at eval_point (eq dot product) ----
        s.claims = _initialClaims(outputEvals, s.point);

        // ---- dim-reducing loop ----
        uint256 numLayers = 18; // 22 - 4
        for (uint256 k = 0; k < numLayers; k++) {
            _layer(s, blob, numEvalPointCoords + k, k == numLayers - 1);
        }

        seedOut = s.seed;
        batchingOut = s.batching;
        pointLen = s.point.length;
    }

    function _layer(St memory s, bytes calldata blob, uint256 foldingSteps, bool boundary)
        internal
        pure
    {
        // initial claim = RLC(claims, batching)
        uint256 claim = 0;
        {
            uint256 cb = 1;
            for (uint256 i = 0; i < s.claims.length; i++) {
                claim = addmod(claim, mulmod(cb, s.claims[i], P), P);
                cb = mulmod(cb, s.batching, P);
            }
        }

        uint256[] memory newPoint = new uint256[](foldingSteps + 1);
        uint256 eqPrefactor = 1;
        bytes32 seed = s.seed;

        // sumcheck rounds
        for (uint256 round = 0; round < foldingSteps; round++) {
            uint256 base = s.off;
            uint256 c0 = _readEl(blob, base);
            uint256 c1 = _readEl(blob, base + 16);
            uint256 c2 = _readEl(blob, base + 32);
            uint256 c3 = _readEl(blob, base + 48);

            // check: claim == (2c0+c1+c2+c3)*eq_prefactor
            uint256 sum01 = addmod(addmod(addmod(mulmod(2, c0, P), c1, P), c2, P), c3, P);
            require(mulmod(sum01, eqPrefactor, P) == claim, "sumcheck round");

            // absorb 4 coeffs (BE16 packing == raw blob slice), draw r
            seed = keccak256(abi.encodePacked(seed, blob[base:base + 64]));
            s.off = base + 64;
            seed = keccak256(abi.encodePacked(seed));
            uint256 r = (uint256(seed) >> 128) % P;

            // claim = horner(c, r)
            claim = addmod(
                mulmod(addmod(mulmod(addmod(mulmod(c3, r, P), c2, P), r, P), c1, P), r, P), c0, P
            );
            // eq_prefactor = (1-r)(1-p) + r*p
            uint256 p = s.point[round];
            eqPrefactor =
                addmod(mulmod(_sub(1, r), _sub(1, p), P), mulmod(r, p, P), P);
            newPoint[round] = r;
        }

        // ---- final step ----
        uint256 finalClaim = claim;
        uint256 finalEq = eqPrefactor;

        // 10 LSB lines in sorted order at blob[off .. off+320]
        uint256 lsbBase = s.off;
        // logical order (identity for cascade; global_output_map perm for boundary)
        uint256[10] memory perm =
            boundary ? _boundaryPerm() : [uint256(0), 1, 2, 3, 4, 5, 6, 7, 8, 9];

        uint256 g;
        {
            uint256 cb = 1;
            // slot 0
            g = _accProd(g, cb, blob, lsbBase + perm[0] * 32);
            cb = mulmod(cb, s.batching, P);
            // slot 1
            g = _accProd(g, cb, blob, lsbBase + perm[1] * 32);
            cb = mulmod(cb, s.batching, P);
            // lookup pairs (2,3),(4,5),(6,7)
            for (uint256 t = 0; t < 3; t++) {
                uint256 ni = 2 + t * 2;
                uint256 di = ni + 1;
                uint256 v0a = _readEl(blob, lsbBase + perm[ni] * 32);
                uint256 v0b = _readEl(blob, lsbBase + perm[ni] * 32 + 16);
                uint256 v1a = _readEl(blob, lsbBase + perm[di] * 32);
                uint256 v1b = _readEl(blob, lsbBase + perm[di] * 32 + 16);
                uint256 num = addmod(mulmod(v0a, v1b, P), mulmod(v0b, v1a, P), P);
                uint256 den = mulmod(v1a, v1b, P);
                g = addmod(g, mulmod(cb, num, P), P);
                cb = mulmod(cb, s.batching, P);
                g = addmod(g, mulmod(cb, den, P), P);
                cb = mulmod(cb, s.batching, P);
            }
            // slot 8
            g = _accProd(g, cb, blob, lsbBase + perm[8] * 32);
            cb = mulmod(cb, s.batching, P);
            // slot 9
            g = _accProd(g, cb, blob, lsbBase + perm[9] * 32);
        }

        require(mulmod(g, finalEq, P) == finalClaim, "final-step check");

        // absorb LSB lines in SORTED order (raw blob slice), draw [r_last, next_batching]
        seed = keccak256(abi.encodePacked(seed, blob[lsbBase:lsbBase + 320]));
        s.off = lsbBase + 320;
        seed = keccak256(abi.encodePacked(seed));
        uint256 rLast = (uint256(seed) >> 128) % P;
        seed = keccak256(abi.encodePacked(seed));
        uint256 nextBatching = (uint256(seed) >> 128) % P;
        newPoint[foldingSteps] = rLast;

        // next claims = LSB (logical order) interpolated at r_last
        uint256[] memory nextClaims = new uint256[](10);
        for (uint256 i = 0; i < 10; i++) {
            uint256 l0 = _readEl(blob, lsbBase + perm[i] * 32);
            uint256 l1 = _readEl(blob, lsbBase + perm[i] * 32 + 16);
            nextClaims[i] = addmod(mulmod(_sub(l1, l0), rLast, P), l0, P);
        }

        s.seed = seed;
        s.batching = nextBatching;
        s.point = newPoint;
        s.claims = nextClaims;
    }

    function _accProd(uint256 g, uint256 cb, bytes calldata blob, uint256 elOff)
        internal
        pure
        returns (uint256)
    {
        uint256 l0 = _readEl(blob, elOff);
        uint256 l1 = _readEl(blob, elOff + 16);
        return addmod(g, mulmod(cb, mulmod(l0, l1, P), P), P);
    }

    function _initialClaims(bytes calldata outputEvals, uint256[] memory point)
        internal
        pure
        returns (uint256[] memory claims)
    {
        uint256 n = point.length; // 4
        uint256 size = 1 << n; // 16
        uint256[] memory eq = new uint256[](size);
        for (uint256 j = 0; j < size; j++) {
            uint256 e = 1;
            for (uint256 v = 0; v < n; v++) {
                uint256 bit = (j >> (n - 1 - v)) & 1;
                uint256 f = bit == 1 ? point[v] : _sub(1, point[v]);
                e = mulmod(e, f, P);
            }
            eq[j] = e;
        }
        claims = new uint256[](10);
        for (uint256 col = 0; col < 10; col++) {
            uint256 acc = 0;
            for (uint256 j = 0; j < size; j++) {
                uint256 val = _readEl(outputEvals, (col * size + j) * 16);
                acc = addmod(acc, mulmod(val, eq[j], P), P);
            }
            claims[col] = acc;
        }
    }

    function _readEl(bytes calldata b, uint256 off) internal pure returns (uint256) {
        return uint256(uint128(bytes16(b[off:off + 16])));
    }

    function _sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return addmod(a, P - b, P);
    }
}
