`alt_whir_calldata.hex`: the two-tx WHIR calldata of a DIFFERENT 2^21 wrap proof with the same
shape (W3 integration `l1-integration` ec1054ff9, `verifier_evm/debug_data/l1_wrap_2p21/`, final PC
267032). The WHIR verifier source is identical for both proofs, so it verifies on its own; with
this proof's GKR half it must not. Used only by `test_rejects_mismatched_halves`.
