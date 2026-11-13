# The Lean CI job's container (ci/sim.sh): ubuntu:24.04 as in the workflow, with the packages of its `deps` step baked
# in (the workflow installs them on every run, ~1 min). The Sail model's packages (`sail-deps`) are installed by the
# job when the Sail cache misses, as in the workflow. Native arch: on an arm64 host this is linux/arm64.
FROM ubuntu:24.04
COPY lean-ci.sh /opt/fvci/lean-ci.sh
RUN /opt/fvci/lean-ci.sh deps && rm -rf /var/lib/apt/lists/*
ENV PATH=/root/.elan/bin:$PATH
WORKDIR /w
