`alt_whir_stream.hex`: the WHIR proof stream of ANOTHER valid 2^21 wrap proof with the version's
shape. With this proof's GKR stream it must not verify. Used only by `test_rejects_mismatched_halves`.
Written by `AB_EVM_VERSION=2p21 AB_ALT_L1_PROOF=<proof.json> AB_ALT_L1_AUX=<aux.json> cargo test
-p verifier_evm --release --test alt_whir_calldata -- --ignored`, which also rewrites the line below.
Current file: unified_circuit_proof_proth120_2p21.json (keccak256 d696c50d39c9b53013a8573f4331b0ce86d0ed9ddab19a80189e78e14ba363e4), final PC 267028.
