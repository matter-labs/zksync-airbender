`alt_whir_calldata.hex`: the two-tx WHIR calldata of ANOTHER valid 2^21 wrap proof with the version's
shape. The WHIR verifier source is the same for both proofs, so it verifies on its own; with this
proof's GKR half it must not. Used only by `test_rejects_mismatched_halves`. Written by
`AB_EVM_VERSION=2p21 AB_ALT_L1_PROOF=<proof.json> AB_ALT_L1_AUX=<aux.json> cargo test -p verifier_evm
--test alt_whir_calldata -- --ignored`, which also rewrites the line below.
Current file: unified_circuit_proof_proth120_2p21.json (keccak256 d696c50d39c9b53013a8573f4331b0ce86d0ed9ddab19a80189e78e14ba363e4), final PC 267028.
