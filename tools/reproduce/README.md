# Building reproducible verifiers

The verifier guest binaries under `tools/gkr_verifier` (`fsv_*` full-statement verifiers
and the per-circuit profiled verifiers) are committed and must be byte-identical whoever
rebuilds them. Run, from any directory:

```shell
./tools/reproduce/reproduce.sh
```

It uses the native toolchain pinned by `tools/gkr_verifier/rust-toolchain.toml` (rustup
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
`git diff --stat tools/gkr_verifier` shows what a source change moved.
