# Use a specific version of Rust for reproducibility
FROM debian:bullseye-slim as builder

RUN apt-get update && apt-get install -y \
    curl \
    build-essential \
    git \
    libssl-dev \
    pkg-config

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain nightly-2025-05-24
ENV PATH="/root/.cargo/bin:${PATH}"

RUN rustup target add riscv32i-unknown-none-elf
RUN cargo install cargo-binutils
RUN rustup component add llvm-tools-preview



# RUN git clone  --depth 1 -b mmzk_0608_reproduce  https://github.com/matter-labs/zksync-airbender.git
COPY . zksync-airbender

WORKDIR zksync-airbender/tools/verifier

RUN ./build.sh