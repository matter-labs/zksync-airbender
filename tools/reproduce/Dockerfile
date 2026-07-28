# Use a specific version of Rust for reproducibility
# FROM debian:bullseye-slim as builder
FROM debian:bullseye-slim@sha256:f527627d07c18abf87313c341ee8ef1b36f106baa8b6b6dc33f4c872d988b651 AS builder

RUN apt-get update && apt-get install -y \
    curl \
    build-essential \
    git \
    libssl-dev \
    pkg-config \
    && rm -rf /var/lib/apt/lists/*

# The verifier binaries build on STABLE Rust. This must stay in sync with the
# channel pinned in `../gkr_verifier/rust-toolchain.toml`. The build still needs
# a few unstable options (`-Z build-std`, `-Z panic-immediate-abort`, the
# `[unstable]` config section, and the `cargo-features` manifest flag); those are
# unlocked with the `RUSTC_BOOTSTRAP=1` trick set inside `dump_bin.sh`, so no
# nightly toolchain is required.
ENV RUST_VERSION=1.97.1

ENV PATH="/root/.cargo/bin:${PATH}"

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain "$RUST_VERSION" \
    && rustup target add riscv32i-unknown-none-elf \
    && rustup component add llvm-tools \
    && rustup component add rust-src \
    && cargo install cargo-binutils

COPY . zksync-airbender

WORKDIR zksync-airbender/tools/gkr_verifier

# Build the full-statement-verifier (fsv_*) RISC-V binaries in every blake
# variant / security level the recursion pipeline can select. The toolchain is
# pinned to $RUST_VERSION by this crate's rust-toolchain.toml; RUSTC_BOOTSTRAP=1
# (set inside dump_bin.sh) unlocks the unstable build options on stable.
RUN ./dump_recursive_verifiers.sh
