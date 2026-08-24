# Use a specific version of Rust for reproducibility
# FROM debian:bullseye-slim as builder
FROM debian:bullseye-slim@sha256:f527627d07c18abf87313c341ee8ef1b36f106baa8b6b6dc33f4c872d988b651 AS builder

# Freeze APT to a point in time. Without this, `apt-get install` pulls whatever Debian
# serves today, so the compiler and linker used by the build drift over time -- the most
# likely reason two runs of the same commit produced different verifier binaries.
ARG DEBIAN_SNAPSHOT=20250811T000000Z
RUN set -eux; \
    printf 'Acquire::Check-Valid-Until "false";\n' > /etc/apt/apt.conf.d/99snapshot; \
    printf 'Acquire::http::No-Cache "true";\n'     > /etc/apt/apt.conf.d/99no-cache; \
    echo "deb [check-valid-until=no] http://snapshot.debian.org/archive/debian/${DEBIAN_SNAPSHOT} bullseye main"                   >  /etc/apt/sources.list; \
    echo "deb [check-valid-until=no] http://snapshot.debian.org/archive/debian-security/${DEBIAN_SNAPSHOT} bullseye-security main" >> /etc/apt/sources.list

# Timestamps and locale/timezone leak into build outputs; pin them all.
# SOURCE_DATE_EPOCH is passed in by reproduce.sh from the last commit date.
ARG SOURCE_DATE_EPOCH=1700000000
ENV SOURCE_DATE_EPOCH=${SOURCE_DATE_EPOCH} \
    CARGO_INCREMENTAL=0 \
    TZ=UTC LANG=C.UTF-8 LC_ALL=C.UTF-8

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
ENV RUST_VERSION=1.98.0

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain "$RUST_VERSION"

ENV PATH="/root/.cargo/bin:${PATH}"

RUN rustup target add riscv32i-unknown-none-elf
RUN rustup component add llvm-tools
RUN rustup component add rust-src
RUN cargo install cargo-binutils --version '=0.4.0'

COPY . zksync-airbender

WORKDIR zksync-airbender/tools/gkr_verifier

# Build the full-statement-verifier (fsv_*) RISC-V binaries in every blake
# variant / security level the recursion pipeline can select. The toolchain is
# pinned to $RUST_VERSION by this crate's rust-toolchain.toml; RUSTC_BOOTSTRAP=1
# (set inside dump_bin.sh) unlocks the unstable build options on stable.
RUN ./dump_recursive_verifiers.sh
