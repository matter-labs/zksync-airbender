# The Lean CI job's container (ci/sim.sh): ubuntu:24.04 as in the workflow, with the apt packages its steps install
# baked in (the workflow installs them on every run; their time is apt's, not the build's). Native arch: on an arm64
# host this is linux/arm64, no emulation.
FROM ubuntu:24.04
COPY lean-ci.sh /opt/fvci/lean-ci.sh
RUN /opt/fvci/lean-ci.sh deps && /opt/fvci/lean-ci.sh sail-deps && rm -rf /var/lib/apt/lists/*
ENV PATH=/root/.elan/bin:$PATH
WORKDIR /w
