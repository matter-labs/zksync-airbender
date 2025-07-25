# Use a specific version of Rust for reproducibility
# FROM debian:bullseye-slim as builder
FROM debian:bullseye-slim@sha256:f527627d07c18abf87313c341ee8ef1b36f106baa8b6b6dc33f4c872d988b651 AS builder

RUN apt-get update && apt-get install -y \
    curl \
    build-essential \
    git \
    libssl-dev \
    pkg-config

# version MUST be the same as in /tools/verifier/rust-toolchain.toml    
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain nightly-2025-07-25
ENV PATH="/root/.cargo/bin:${PATH}"

RUN rustup target add riscv32i-unknown-none-elf
RUN rustup component add llvm-tools-preview
RUN rustup component add rust-src
RUN cargo install cargo-binutils

# RUN git clone  --depth 1 -b mmzk_0608_reproduce  https://github.com/matter-labs/zksync-airbender.git
COPY . zksync-airbender

WORKDIR zksync-airbender/tools/verifier

RUN ./build.sh