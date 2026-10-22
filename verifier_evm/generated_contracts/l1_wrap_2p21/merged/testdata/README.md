`alt_whir_stream.hex`: the WHIR proof stream of ANOTHER valid 2^21 wrap proof with the version's
shape. With this proof's GKR stream it must not verify. Used only by `test_rejects_mismatched_halves`.
Written by `AB_EVM_VERSION=2p21 AB_ALT_L1_PROOF=<proof.json> AB_ALT_L1_AUX=<aux.json> cargo test
-p verifier_evm --release --test alt_whir_calldata -- --ignored`, which also rewrites the line below.
Current file: l1_wrap_alt_dynamic_fibonacci_1000.json (keccak256 6c4a144e341e7e131328882a161fcf98a356c6d3901f7c16943551d5da5629a8), final PC 263568.
