# Zero-timestamp phantom delegation PoC

This branch starts from `av_gkr_compiler` at `8eeca806016eff359dab694b8c8587c61fedb3f3`. Its three-instruction guest has no Keccak delegation call and does not touch x10 or x11. The PoC inserts one active Keccak row with invocation timestamp zero. Its CSR read and write tuples cancel, while the row changes the initial x10 state observed by the guest from 0 to 8 at timestamp 2. The Keccak transition constrains that value; it is not a free witness.

The committed fixture can be checked directly from this worktree:

```sh
cd full_statement_verifier
cargo test --test unified --features verifiers,proof_utils unified_base_layer_accepts_zero_ts_phantom -- --ignored --nocapture
```

To regenerate the PoC fixture and compare against the unmodified control:

```sh
cd prover
cargo test --profile cli --lib gkr_run_unified_zero_ts_phantom_sec_100 -- --ignored --nocapture
cargo test --profile cli --lib gkr_run_unified_zero_ts_control_sec_100 -- --ignored --nocapture
cd ../full_statement_verifier
cargo test --test unified --features verifiers,proof_utils unified_base_layer_accepts_zero_ts_phantom -- --ignored --nocapture
cargo test --test unified --features verifiers,proof_utils unified_base_layer_accepts_zero_ts_control -- --ignored --nocapture
```

Both proofs close the memory permutation and pass the vulnerable full-statement verifier. The phantom fixture exports x10 = 8 at timestamp 2; the control exports x10 = 0 at timestamp 0. The fix branch `mb_fix_delegation_zero_ts_v3` rejects the phantom fixture after regeneration.
