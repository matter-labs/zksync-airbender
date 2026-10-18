`alt_whir_stream.hex`: the WHIR proof stream of ANOTHER valid 2^21 wrap proof with the version's
shape. With this proof's GKR stream it must not verify. Used only by `test_rejects_mismatched_halves`.
Written by `AB_EVM_VERSION=2p21 AB_ALT_L1_PROOF=<proof.json> AB_ALT_L1_AUX=<aux.json> cargo test
-p verifier_evm --release --test alt_whir_calldata -- --ignored`, which also rewrites the line below.
Current file: alt-l1-wrap-proof.json (keccak256 13f3c6eb3ee86f9a4713f5c6efdb8fc2637420bac83a078ceb96c04c5f218d18), final PC 266852.
