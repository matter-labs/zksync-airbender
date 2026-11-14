"""Print one root-workspace clippy run for the guest whose `cargo metadata` is on stdin.

usage: guest_dependencies.py REPO_ROOT GUEST_CARGO_CONFIG
Output: the guest's target features, then `-p` and `--features` for every root-workspace crate
the guest build resolves, with the features it resolves for each.
"""

import json
import os
import re
import sys

repo_root, config_path = sys.argv[1], sys.argv[2]
metadata = json.load(sys.stdin)
# The CI runner's Python predates tomllib; the configs list the flag as one string.
with open(config_path) as config:
    target_features = re.search(r'"target-feature=([^"]+)"', config.read()).group(1)
packages = {package["id"]: package for package in metadata["packages"]}
guest_root = metadata["workspace_root"] + os.sep
arguments = []
for node in sorted(metadata["resolve"]["nodes"], key=lambda node: packages[node["id"]]["name"]):
    package = packages[node["id"]]
    directory = os.path.dirname(package["manifest_path"]) + os.sep
    if package["source"] is None and directory.startswith(repo_root + os.sep) and not directory.startswith(guest_root):
        arguments += ["-p", package["name"]]
        arguments += [f"--features={package['name']}/{feature}" for feature in node["features"]]
print(target_features, " ".join(arguments))
