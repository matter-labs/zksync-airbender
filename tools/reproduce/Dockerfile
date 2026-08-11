# Use a specific version of Rust for reproducibility
# FROM debian:bullseye-slim as builder
# Platform is pinned as well as the digest: the same digest on a different architecture
# would still produce different binaries.
FROM --platform=linux/amd64 debian:bullseye-slim@sha256:f527627d07c18abf87313c341ee8ef1b36f106baa8b6b6dc33f4c872d988b651 AS builder

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
# SOURCE_DATE_EPOCH is a fixed constant, not the commit date: it has to stay the same
# across commits, otherwise the artifacts committed at one commit stop reproducing at the
# next and check_verifiers fails on unrelated changes. The exact value is arbitrary
# (2023-11-14); only its stability matters. Changing it invalidates every committed
# artifact, so it should be treated as frozen.
ARG SOURCE_DATE_EPOCH=1700000000
# How many verifier builds build.sh runs concurrently. 0 = all at once, which is what CI
# uses. Lower it (e.g. 3) on machines that cannot hold twelve concurrent rustc processes
# in memory. It only changes scheduling, so the artifacts must come out identical either
# way -- if they do not, that is a reproducibility bug worth knowing about.
ARG AIRBENDER_BUILD_JOBS=0

ENV SOURCE_DATE_EPOCH=${SOURCE_DATE_EPOCH} \
    AIRBENDER_BUILD_JOBS=${AIRBENDER_BUILD_JOBS} \
    CARGO_INCREMENTAL=0 \
    TZ=UTC LANG=C.UTF-8 LC_ALL=C.UTF-8

# ca-certificates is listed explicitly: it used to arrive as an apt "recommends", which
# --no-install-recommends now excludes, and without it curl cannot verify TLS.
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    build-essential \
    git \
    libssl-dev \
    pkg-config \
 && rm -rf /var/lib/apt/lists/*

# version MUST be the same as in /tools/verifier/rust-toolchain.toml    
# Fetch and run as separate steps rather than `curl | sh`: in a pipeline the step's exit
# status is the shell's, not curl's, so a failed download silently produced an image with
# no toolchain and the build only fell over several steps later.
RUN set -eux; \
    curl -sSf https://sh.rustup.rs -o /tmp/rustup-init.sh; \
    sh /tmp/rustup-init.sh -y --default-toolchain nightly-2025-07-25; \
    rm -f /tmp/rustup-init.sh
ENV PATH="/root/.cargo/bin:${PATH}"

RUN rustup target add riscv32i-unknown-none-elf
RUN rustup component add llvm-tools-preview
RUN rustup component add rust-src
# --locked so cargo-binutils and its dependency tree do not float between runs.
RUN cargo install cargo-binutils --locked

# RUN git clone  --depth 1 -b mmzk_0608_reproduce  https://github.com/matter-labs/zksync-airbender.git
COPY . zksync-airbender

WORKDIR zksync-airbender/tools/verifier

# Two layers on purpose: if key generation fails, the binaries stay cached and the next
# attempt only redoes the keys instead of recompiling all twelve verifiers.
RUN AIRBENDER_SKIP_VK=1 ./build.sh

# Declared here, after the binaries: an ARG/ENV placed earlier becomes part of the cache
# key for every later layer, so tuning key-generation concurrency would invalidate the
# compile step and rebuild all twelve verifiers. Defaults to AIRBENDER_BUILD_JOBS.
ARG AIRBENDER_VK_JOBS=
ENV AIRBENDER_VK_JOBS=${AIRBENDER_VK_JOBS}
RUN ./build_vk.sh
