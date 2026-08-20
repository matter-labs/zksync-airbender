# WHIR contract accepted trailing proof calldata

## Classification

- Confirmed historical L1 proof-parser malleability bug
- Boundary: WHIR proof byte stream → registry success notification
- Component: final calldata cursor/exhaustion check
- Security character: noncanonical proof encodings and integration ambiguity; no standalone algebraic forgery established
- Fixed by: [`4b0d431`](https://github.com/matter-labs/zksync-airbender/commit/4b0d43104b7a82b5b9bec7fc37a6d6bea0c94cb8)
- Vulnerable revision: `585e7c9384f83e2d6b98023d8aa5bdd001686faa`

## Boundary context

The WHIR contract parses a compact, configuration-dependent stream directly from calldata. Its cursor advances through commitments, OOD values, terminal monomials, PoW nonces, and query openings. After the final round it notifies a registry that verification of the committed handoff state succeeded.

For a bare proof entrypoint, the accepted language should contain exactly the bytes consumed by that grammar. Solidity's ability to ignore trailing calldata is not a protocol decision unless an outer envelope explicitly owns those bytes.

## Intended parser contract

```text
cursor starts at configured proof-stream offset
every proof object advances cursor by its canonical encoded length
after final query: cursor == calldatasize()
only then call/notify the registry and return success
```

The split GKR stream had an intentional handoff framing distinction, but the WHIR stream ended at calldata end.

## Failure

After processing the final WHIR query, the contract never compared its cursor with `calldatasize()`. Any suffix—one byte, full words, or an encoded second object—was silently ignored while the same registry success path executed.

All cryptographic checks covered only the consumed prefix. The unconsumed suffix had no authenticated interpretation.

## Failure flow

1. Take a valid canonical WHIR calldata payload.
2. Append arbitrary bytes.
3. Submit the longer calldata to the same verifier entrypoint.
4. Parser consumes the original prefix and stops.
5. Contract reports success/updates registry exactly as for the canonical encoding.

This does not by itself prove a false polynomial statement. It creates multiple accepted byte identities for one proof, which can break relayer deduplication, signed-calldata authorization, proof hashing, recursive handoff assumptions, or future concatenated-message parsing.

## Impact and fix

The L1 verifier accepted a prefix language rather than an exact proof language. The fix requires `REG_CD == calldatasize()` after all rounds and reverts before registry notification on any suffix.

Cursor exhaustion is a boundary invariant, not cosmetic strictness. Review zero-padding reads, ABI selector/length framing, intentional envelopes, and downstream proof-identity consumers together.

## Regression

- Append 1, 15, 16, 31, and 32 bytes to valid calldata and require revert.
- Truncate at every object boundary and require revert.
- Verify intentional GKR-to-WHIR framing bytes are owned by exactly one parser.
- Compare proof hash/deduplication keys with the exact accepted byte stream.
- Confirm failure prevents external registry calls and persistent-state updates.

## Reproduction evidence

```sh
git diff 585e7c9384f83e2d6b98023d8aa5bdd001686faa 4b0d43104b7a82b5b9bec7fc37a6d6bea0c94cb8 -- verifier_evm/src/templates/whir.sol
```
