#!/usr/bin/env python3
"""Build native consumer-role, cache or lookup instances serially under bounded_fv.py."""
import argparse
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=FAMILIES, action="append")
    parser.add_argument("--stage", choices=("typing", "cache", "lookup"), default="typing")
    args = parser.parse_args()
    environment = dict(os.environ, LEAN_NUM_THREADS="1")
    for family, stem in zip(FAMILIES, CASES):
        if args.family and family not in args.family:
            continue
        for suffix in ("Uncached", "Cached"):
            namespace = {"typing": "ConsumerNative", "cache": "CacheNative", "lookup": "LookupNative"}[args.stage]
            name = "GKRProtocol." + namespace + "." + stem + suffix
            print("CONSUMER " + args.stage.upper(), name, flush=True)
            subprocess.run(["lake", "--no-cache", "build", "+" + name + ":olean"],
                           cwd=LEAN, env=environment, check=True)


if __name__ == "__main__":
    main()
