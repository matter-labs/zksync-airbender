# `fuzzing`

This crate contains fuzzing and differential-testing utilities for several parts of the project.

## Usage


### `rv32im-afl`

`rv32im-afl` runs AFL-based fuzzing for the RV32IM path. Requires installing AFL as follows:

```bash
cargo install cargo-afl
cargo afl system-config
```

Current CLI arguments:

- `--mode <MODE>`: fuzzing mode.
- `--test-one`: process a single AFL input and stop.

Supported modes:

- `--mode dumb`: feeds random binaries directly into the VM target.
- `--mode unicorn`: runs the input on both the target VM and Unicorn and aborts on register mismatches.

Use `cargo afl fuzz -h` to see instructions on how to run AFL++.

Examples:

```bash
cargo afl build -p fuzzing --bin rv32im-afl
cargo afl fuzz -i fuzzing-runs/rv32im-1/in -o fuzzing-runs/rv32im-1/out -- target/debug/rv32im-afl --mode dumb
```

```bash
cargo afl build -p fuzzing --bin rv32im-afl
cargo afl fuzz -i fuzzing-runs/rv32im-1/in -o fuzzing-runs/rv32im-1/out -- target/debug/rv32im-afl --mode unicorn --test-one
```

### `prover-fuzz`

`prover-fuzz` provides a prover-oriented fuzzing scaffold plus an offline crash-triage command.

This binary is only available when the `prover` feature is enabled.

Main fuzzing arguments:

- `--input-dir <PATH>`: directory containing seed `.bin` / `.text` pairs.
- `--output-dir <PATH>`: directory where cache entries and crashes are written.
- `--iterations <N>`: optional number of fuzz-loop iterations.
- `--seed <N>`: optional RNG seed for reproducible runs.
- `--skip-validation`: skip the initial seed-validation pass.

Example:

```bash
cargo run -p fuzzing --features prover --bin prover-fuzz -- \
  --input-dir fuzzing/tests/compliance-tests-programs \
  --output-dir /tmp/prover-fuzz \
  --iterations 100 \
  --seed 1
```

#### `prover-fuzz triage`

The `triage` subcommand replays a persisted crash artifact and compares it against the cached base seed.

Triage arguments:

- `--crash <PATH>`: path to the crash artifact JSON file.
- `--output-dir <PATH>`: output directory used by the original fuzzing run.
- `--json`: print the report as JSON.

Example:

```bash
cargo run -p fuzzing --features prover --bin prover-fuzz -- \
  triage \
  --crash /tmp/prover-fuzz/crashes/example.json \
  --output-dir /tmp/prover-fuzz \
  --json
```


### `witgen-fuzz`

`witgen-fuzz` runs witness-generation fuzzing for a selected circuit target and then applies a selected consistency check to the collected samples.

Current CLI arguments:

- `--circuit <CIRCUIT>`: target circuit to fuzz.
- `--check <CHECK>`: check to run on the collected witnesses.
- `--samples <N>`: number of samples to collect. Defaults to `1`.

Currently supported values in the source:

- `--circuit add-sub-lui-auipc-mop`
- `--check linear-constraints`

Example:

```bash
cargo run -p fuzzing --bin witgen-fuzz -- \
  --circuit add-sub-lui-auipc-mop \
  --check linear-constraints \
  --samples 100
```

## Compliance Tests

These tests check whether the transpiler and the circuits satisfy the RISC-V ISA specification. They are based on the [`riscv-arch-test`](https://github.com/riscv/riscv-arch-test) suite.

### Generating the test binaries

The generated test binaries are already bundled in `fuzzing/tests/compliance-tests-programs`, so most users do not need to regenerate them.

If regeneration is needed, follow the instructions in [`riscv-arch-test`](https://github.com/riscv/riscv-arch-test) (`act4` branch) using the custom configuration bundle in `fuzzing/tests/compliance-tests-config`. 
Install the tools as per their instructions, then generate the test binaries:

```bash
CONFIG_FILES=fuzzing/tests/compliance-tests-config/test_config.yaml make --jobs $(nproc) -C <path to riscv-arch-test>
```

If needed, set `WORKDIR=...` as well. The generated ELFs will be written under `<workdir>/zksync-rv32im/elfs`.
Refer to their documentation for more details on how to generate the tests.

After generation, copy the `.elf` files into `fuzzing/tests/compliance-tests-programs`, then run:

```bash
bash fuzzing/tests/compliance-tests-programs/extract-bins.sh
```

This performs the final preparation step by extracting the `.bin` and `.text` files consumed by the tests.
The command above may have to be executed even if the `.elf` files are not regenerated since the `.bin` and `.text` files are
ignored by git.

### Running the tests

To run the compliance suite against the Unicorn oracle and the target transpiler VM, use:

```bash
cargo test -p fuzzing --profile compliance-tests
```

To also test the prover-related path, enable the `prover` feature:

```bash
cargo test -p fuzzing --profile compliance-tests --features prover
```

On less powerful machines, it is recommended to limit the number of threads:

```bash
cargo test -p fuzzing --profile compliance-tests --features prover -- --test-threads 1
```
