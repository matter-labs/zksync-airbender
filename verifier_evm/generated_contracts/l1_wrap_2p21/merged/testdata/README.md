`alt_whir_stream.hex`: the WHIR proof stream of ANOTHER valid 2^21 wrap proof with the version's
shape. With this proof's GKR stream it must not verify. Used only by `test_rejects_mismatched_halves`.
Written by `AB_EVM_VERSION=2p21 AB_ALT_L1_PROOF=<proof.json> AB_ALT_L1_AUX=<aux.json> cargo test
-p verifier_evm --release --test alt_whir_calldata -- --ignored`, which also rewrites the line below.
Current file: unified_circuit_proof_proth120_2p21.json (keccak256 ffd08dbb6ddfbcb389d0c7b9da926fc9ee65cdf3e9aa3115351aaa61cf8ea681), final PC 263568.
