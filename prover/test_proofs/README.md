# Canonical circuit proofs

The canonical set contains one Sec100 proof for each of 14 circuits in each
soundness mode: `PessimisticConjecture` and `EthproofsSoundnessCalc`.
`PessimisticConjecture` uses `<circuit>_sec_100_gkr_proof.json`;
`EthproofsSoundnessCalc` adds `_ethproofs_soundcalc` after `sec_100`.
G-function has no canonical fixture. Legacy `keccak_special5` remains covered.

Run the sole producer from the repository root:

```sh
RUST_MIN_STACK=16777216 cargo test -p prover --lib --profile cli \
  tests::gkr::canonical_proofs::regenerate_canonical_circuit_proofs \
  -- --exact --nocapture --test-threads=1
```

Use the default features, including `deterministic_pow`, and the regular
generated layouts. The producer reads each circuit's generated Sec100 config
for its mode, uses eight worker threads, and writes pretty JSON without a
trailing newline. It regenerates all 28 files and rejects duplicate writes.

The shared recipe is implemented in
[`canonical_fixtures.rs`](../src/tests/gkr/orchestration/canonical_fixtures.rs).
The CPU producer and GPU tests use its explicit circuit-to-workload mapping.
All workloads have a `2^20` cycle bound. Paths below name the binary/text pair
without their `.bin` and `.text` extensions; reads are ordered `u32` values.
`N` is the generated circuit's trace length as `log2(rows)`.

| Circuit(s) | Workload | Reads | Decoder | RAM | N |
| --- | --- | --- | --- | --- | --- |
| `add_sub_lui_auipc_mop`, `shift_binop` | `examples/mop_smoke/app` | `[15, 1]` | full unsigned | 1 GiB | 24 |
| `jump_branch_slt`, `mem_word_only`, `mem_subword_only`, `inits_and_teardowns` | `riscv_transpiler/examples/keccak_f1600/app` | `[15, 1]` | full unsigned | 512 MiB | 24 |
| `unsigned_mul_div` | `examples/hashed_fibonacci/app_blake2_with_compression` | `[15, 1]` | full unsigned | 1 GiB | 23 |
| `bigint_with_extended_control` | `examples/bigint_with_control/app` | `[]` | full unsigned | 1 GiB | 22 |
| `blake2_with_extended_control` | `examples/multi_family_smoke/app_blake2_with_compression` | `[50, 0xDEADBEEF]` | reduced | 1 GiB | 20 |
| `unified_reduced_machine` | `examples/multi_family_smoke/app_blake2_with_compression` | `[50, 0xDEADBEEF]` | reduced | 1 GiB | 23 |
| `keccak_special5` | `riscv_transpiler/examples/keccak_f1600/app` | `[15, 1]` | full unsigned | 512 MiB | 22 |
| `keccak_column_parity`, `keccak_theta_rho`, `keccak_chi5` | `examples/keccak/app` | `[]` | full unsigned | 512 MiB | 22 |

The recipe checks replayed final state, nonempty selected rows and single-instance
capacity. It checks MOP/byte-swap execution and the three new Keccak row counts.
It collects sparse final RAM before expanding the selected inits/teardowns sets.

Compression and unified form one statement. Their challenges come from the
shared memory transcript, final registers/PC/timestamp and sorted RAM top bits,
with deterministic 19-bit memory/delegation PoW. The producer checks that their
memory commitments match the transcript and that the combined permutation
product is ONE. The other circuits use the recipe's fixed external challenges.
No environment filter, suffix or packing override selects canonical inputs.

The `malicious_*` files serve verifier rejection tests and have separate forge
producers. The canonical producer does not refresh those files.
