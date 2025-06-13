# ┌──────────────────────────────────────────────────────────────────────────┐
# │                             STAGE 1: BUILDER                             │
# └──────────────────────────────────────────────────────────────────────────┘
FROM nvidia/cuda:12.6.0-devel-ubuntu24.04 AS builder

# Install Git (required to clone) and any other build‐time dependencies.
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
        git \
 && rm -rf /var/lib/apt/lists/*

RUN apt update && apt install -y --no-install-recommends cmake git jq libssl-dev pkg-config wget curl && rm -rf /var/lib/apt/lists/*

ENV RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    PATH=/usr/local/cargo/bin:${PATH}


ARG RUST_VERSION=nightly-2025-03-15
ENV RUST_VERSION=${RUST_VERSION}

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain ${RUST_VERSION} && \
    rustup target add x86_64-unknown-linux-gnu && \
    rustup component add rustfmt clippy


WORKDIR /workspace

# 1. Clone and build anvil-zksync
RUN git clone --depth 1 -b boojumos-dev https://github.com/matter-labs/anvil-zksync.git
WORKDIR /workspace/anvil-zksync
RUN cargo +${RUST_VERSION} build --release

# 2. Clone and build zksync-airbender

WORKDIR /workspace/zksync-airbender
COPY . .
RUN ls
RUN CUDAARCHS=80 cargo +${RUST_VERSION} build --release -p zksmith

#RUN git clone --depth 1 -b mmzk_docker https://github.com/matter-labs/zksync-airbender.git
#WORKDIR /workspace/zksync-airbender
#RUN CUDAARCHS=80 cargo +${RUST_VERSION} build --release -p zksmith

# ┌──────────────────────────────────────────────────────────────────────────┐
# │                          STAGE 2: RUNTIME IMAGE                          │
# └──────────────────────────────────────────────────────────────────────────┘
FROM nvidia/cuda:12.6.0-runtime-ubuntu24.04

# Create a non‐root user (optional but recommended)
RUN useradd --no-create-home --shell /usr/sbin/nologin appuser

WORKDIR /app

# Copy only the final binaries from the builder stage
COPY --from=builder /workspace/anvil-zksync/target/release/anvil-zksync /app/anvil-zksync
COPY --from=builder /workspace/zksync-airbender/target/release/zksmith /app/zksmith
COPY --from=builder /workspace/zksync-airbender/examples/zksync_os/app.bin /app/app.bin

# Make sure they’re executable
RUN chmod +x /app/anvil-zksync /app/zksmith

# Copy the entrypoint script that will start both services
COPY docker/anvil-bender/entrypoint.sh /app/entrypoint.sh
RUN chmod +x /app/entrypoint.sh

# Switch to non‐root user (optional)
# Currently cannot do it due to issues with anvil-zksync and telemetry.
#USER appuser

# Declare which ports the two services will listen on:
# anvil-zksync’s default JSON‐RPC port

EXPOSE 8011   

# zksync-airbender’s port
EXPOSE 3030   

# Start both binaries via the entrypoint script
ENTRYPOINT ["/app/entrypoint.sh"]
