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

# The version of compiler must pinned and in sync with the one specified in `../verifier/rust-toolchain.toml`.
ENV RUST_VERSION=nightly-2026-02-10

ENV PATH="/root/.cargo/bin:${PATH}"

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain "$RUST_VERSION" \
    && rustup target add riscv32i-unknown-none-elf \
    && rustup component add llvm-tools-preview \
    && rustup component add rust-src \
    && cargo install cargo-binutils

COPY . zksync-airbender

WORKDIR zksync-airbender/tools/verifier

# Pass rust version to make sure that we're building with the same compiler.
RUN ./build.sh "$RUST_VERSION"
