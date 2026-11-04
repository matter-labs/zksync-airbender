# ZK prover example

`bigint_with_control` performs a single 256-bit addition through the bigint delegation CSR.

The example is intentionally tiny: it adds `1` to a 256-bit value whose low 64-bit limb is
all `1`s, so the result must carry into the next limb. The program returns the first few output
words so tests can confirm both the delegation path and the delegated arithmetic result.

## Rebuilding

If you change `src/main.rs`, rebuild the binary artifacts by running `dump_bin.sh`.
