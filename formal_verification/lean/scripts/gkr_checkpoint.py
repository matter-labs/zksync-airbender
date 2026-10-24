#!/usr/bin/env python3
"""Replay the compiler checkpoint with ordinary Lake dependencies, one job at a time.

Run this script inside bounded_fv.py. Repeat after a 900-second checkpoint to
resume completed modules normally. No timestamps, traces or proof caches are
rewritten. The full semantic-preservation effort extends beyond this checkpoint.
"""
import os
import subprocess
import sys

from export_gkr_translations import LEAN


def main():
    environment = dict(os.environ, LEAN_NUM_THREADS="1")
    for line in (LEAN / "GKRCompiler.lean").read_text().splitlines():
        if line.startswith("import GKRCompiler.Native."):
            target = line.removeprefix("import ")
            print("ARITHMETIC", target, flush=True)
            subprocess.run(["lake", "--no-cache", "build", "+" + target + ":olean"],
                           cwd=LEAN, env=environment, check=True)
    commands = [
        [sys.executable, "scripts/check_gkr_lookup_certificates.py"],
        [sys.executable, "scripts/gkr_wiring_instances.py", "--build"],
        [sys.executable, "scripts/gkr_lookup_instances.py"],
        [sys.executable, "scripts/gkr_consumer_instances.py", "--stage", "cache"],
        [sys.executable, "scripts/gkr_consumer_instances.py", "--stage", "typing"],
        [sys.executable, "scripts/gkr_consumer_instances.py", "--stage", "lookup"],
        [sys.executable, "scripts/gkr_lookup_source_certificate.py", "--check"],
        [sys.executable, "scripts/gkr_consumer_instances.py", "--stage", "source"],
        [sys.executable, "scripts/gkr_table_instances.py", "--check", "--build"],
        [sys.executable, "scripts/gkr_product_instances.py", "--check", "--build"],
    ]
    for command in commands:
        subprocess.run(command, cwd=LEAN, env=environment, check=True)
    for target in ["GKRCompiler", "GKRProtocol", "Tests.GKRCompilerCertificate",
                   "Tests.GKRCompilerWiring", "Tests.GKRLookupFields",
                   "Tests.GKRConsumerTypes", "Tests.GKRCacheBindings",
                   "Tests.GKRLookupReduction", "Tests.GKRBaseEncoding", "Tests.GKRLookupSource",
                   "Tests.GKRSourceTable", "Tests.GKRNativeProduct"]:
        print("CHECKPOINT", target, flush=True)
        subprocess.run(["lake", "--no-cache", "build", "+" + target + ":olean"],
                       cwd=LEAN, env=environment, check=True)


if __name__ == "__main__":
    main()
