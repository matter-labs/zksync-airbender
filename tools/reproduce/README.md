# Building reproducible verifiers

The verifier guest binaries under `tools/gkr_verifier` (`fsv_*` full-statement verifiers
and the per-circuit profiled verifiers) are committed and must be byte-identical whoever
rebuilds them. Run, from any directory:

```shell
./tools/reproduce/reproduce.sh
```

It first regenerates the guest sources for both soundness modes (`pessimistic_conjecture`
and `ethproofs_soundcalc`): the delegation circuits' setup parameters
(`circuit_defs/setups/generated/delegation_parameters_<mode>.rs`, via the `setups` crate's
`generate_delegation_circuits_artifacts` test) and every circuit's verifier
(`verifier/src/generated/<circuit>/<mode>/`, via the `verifier_generator` crate's
`generate_verifiers` test). Then it builds the binaries: the full-statement verifiers of both
modes (`full_statement_verifiers/` and `full_statement_verifiers/ethproofs_soundcalc/`, the set
`verifier_common::fsv_binaries::FSV_REGISTRY` names) and the per-circuit verifiers. It regenerates
`full_statement_verifiers/fsv_manifest.txt`, the pinned decoded-ROM digest of every
full-statement verifier, which the host loader (`full_statement_verifier::host_utils::load_fsv_exact`)
checks before using a guest, and finally runs the registry tests against the rebuilt files.

The build uses the native toolchain pinned by `tools/gkr_verifier/rust-toolchain.toml` (rustup
installs it on first use, including the `rust-src` / `llvm-tools` components and the
`riscv32i-unknown-none-elf` target) plus `cargo-binutils` for `cargo objcopy`:

```shell
cargo install cargo-binutils --version '=0.4.0'
```

No Docker or emulation is needed. The build is made host- and path-independent by:

- `rustc_wrapper.sh`, which pins cargo's `-C metadata` for guest units. cargo derives that
  hash from the absolute path of the `../../*` path dependencies and from the host triple
  (through build-script and proc-macro units); it ends up in every mangled symbol name, and
  symbol order decides the placement of functions and anonymous constants in the image,
  so without the pin the ROM bytes differed between hosts and checkouts.
- `dump_bin.sh`, which remaps the checkout root, the toolchain sysroot and the cargo
  registry to fixed prefixes in DWARF and strips the `.comment` section (rustc/LLD build
  strings, which differ between the dist toolchains of different hosts) from the `.elf`.

After the script finishes, `git status` must be clean for an already-committed commit;
`git diff --stat tools/gkr_verifier verifier/src/generated circuit_defs/setups/generated` shows
what a source change moved. A moved full-statement verifier also moves its manifest row; commit
both together.
