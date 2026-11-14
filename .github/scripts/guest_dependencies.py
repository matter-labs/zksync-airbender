"""Print one root-workspace clippy run for the guest whose `cargo metadata` is on stdin.

usage: guest_dependencies.py REPO_ROOT GUEST_CARGO_CONFIG
Output: the guest's target features, then `-p` and `--features` for every root-workspace crate
the guest build resolves, with the features it resolves for each.
"""

import json
import os
import sys
import tomllib

repo_root, config_path = sys.argv[1], sys.argv[2]
metadata = json.load(sys.stdin)
with open(config_path, "rb") as config:
    rustflags = tomllib.load(config)["build"]["rustflags"]
target_features = next(flag for flag in rustflags if flag.startswith("target-feature="))
packages = {package["id"]: package for package in metadata["packages"]}
guest_root = metadata["workspace_root"] + os.sep
arguments = []
for node in sorted(metadata["resolve"]["nodes"], key=lambda node: packages[node["id"]]["name"]):
    package = packages[node["id"]]
    directory = os.path.dirname(package["manifest_path"]) + os.sep
    if package["source"] is None and directory.startswith(repo_root + os.sep) and not directory.startswith(guest_root):
        arguments += ["-p", package["name"]]
        arguments += [f"--features={package['name']}/{feature}" for feature in node["features"]]
print(target_features.removeprefix("target-feature="), " ".join(arguments))
