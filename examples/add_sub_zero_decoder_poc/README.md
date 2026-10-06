# Add-sub zero-decoder PoC ROM

The 28-byte RISC-V program has two paths with the same final PC (24):

| PC | Word | Honest action |
| --- | --- | --- |
| 0 | `00000097` | `auipc ra, 0` |
| 4 | `00c08093` | `addi ra, ra, 12` |
| 8 | `00008067` | `jalr x0, ra, 0` |
| 12 | `00100513` | `addi a0, x0, 1` |
| 16 | `0080006f` | `jal x0, 8` |
| 20 | `00200513` | `addi a0, x0, 2` |
| 24 | `0000006f` | `jal x0, 0` (finish loop) |

The authenticated ROM takes the `a0 = 1` path. A prover-only tape mutation of
PC 0 to `Auipc { rd: 0, imm: 8 }` writes 8 to x0 while the zero decoder lookup
hides that row from the true ROM table. The next ADDI reads x0 as its dummy
second source in this circuit, so it sets ra to 20. JALR restores x0 to zero
and jumps to PC 20, producing `a0 = 2` at the same final PC. The mutation must
be applied to the prover-side tape and decoder witness only; `app.bin`,
`app.text`, and the verifier's ROM setup remain exactly these bytes.

The standalone GKR PoC lives in
`experiments_runner/tests/add_sub_zero_decoder_poc.rs`. Its test mutates the
add/sub witness only; genuine ROM data is supplied to the setup commitment.
The stock prover caches only the declared table rows, so the PoC-only hook in
`prover/src/gkr/prover/setup.rs` extends that private lookup cache with the
committed zero padding rows. The witness redirects the first decoder lookup
and its multiplicity to row `2^20`. This prover-side change is necessary to
exercise the verifier's actual acceptance condition.

From `experiments_runner/`, run:

```sh
cargo test -p experiments_runner --test add_sub_startup_vm
AIRBENDER_ADD_SUB_ZERO_POC=1 cargo test --profile cli -p experiments_runner --test add_sub_zero_decoder_poc -- --ignored --nocapture
```

The forged proof is written to
`prover/test_proofs/add_sub_zero_decoder_poc_sec_100_gkr_proof.json`. From
`verifier/`, confirm it against the generated unfixed verifier with:

```sh
cargo test --profile cli -p verifier --test mop_montgomery verifier_add_sub_zero_decoder_poc -- --ignored
```

The standalone verifier accepts the add/sub circuit proof. The full unrolled
statement proof test in `program_prover/src/unrolled.rs` is a separate,
resource-intensive check of global memory and program composition.
