`alt_whir_calldata.hex`: the two-tx WHIR calldata of ANOTHER valid 2^21 wrap proof with the version's
shape. The WHIR verifier source is the same for both proofs, so it verifies on its own; with this
proof's GKR half it must not. Used only by `test_rejects_mismatched_halves`. Written by
`AB_EVM_VERSION=2p21 AB_ALT_L1_PROOF=<proof.json> AB_ALT_L1_AUX=<aux.json> cargo test -p verifier_evm
--test alt_whir_calldata -- --ignored`, which also rewrites the line below.
Current file: W3 integration `l1-integration` ec1054ff9 (final PC 267032).
