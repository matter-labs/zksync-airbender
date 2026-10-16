`alt_whir_stream.hex`: the WHIR proof stream of ANOTHER valid 2^21 wrap proof with the version's
shape. With this proof's GKR stream it must not verify. Used only by `test_rejects_mismatched_halves`.
Written by `AB_EVM_VERSION=2p21 AB_ALT_L1_PROOF=<proof.json> AB_ALT_L1_AUX=<aux.json> cargo test
-p verifier_evm --release --test alt_whir_calldata -- --ignored`, which also rewrites the line below.
Current file: unified_circuit_proof_proth120_2p21.json (keccak256 f91b66d7c2754adacc01fbf2b28e772515492dd5100a01f40be92dc048ae23f9), final PC 267028.
