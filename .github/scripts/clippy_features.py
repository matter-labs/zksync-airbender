"""Print every workspace feature that builds on the host, as a `cargo --features` list.

A feature is left out when it enables one of `EXCLUDED`, directly or through other workspace
features. The guest-only features do not compile on the host; the Miri features need test
inputs that miri.yml generates before it lints those targets.
"""

import json
import subprocess

EXCLUDED = {
    "field/modular_ops",
    "riscv_common/boot_sequence",
    "full_statement_verifier/miri_fsv",
    "verifier/miri_circuits",
    "verifier/miri_compression",
}

metadata = json.loads(
    subprocess.run(
        ["cargo", "metadata", "--no-deps", "--format-version", "1"],
        check=True,
        stdout=subprocess.PIPE,
    ).stdout
)
packages = {package["name"]: package for package in metadata["packages"]}


def reaches_excluded(package, feature, seen):
    key = f"{package['name']}/{feature}"
    if key in seen:
        return False
    seen.add(key)
    if key in EXCLUDED:
        return True
    for value in package["features"].get(feature, []):
        dependency, _, dependency_feature = value.partition("/")
        if not dependency_feature:
            if reaches_excluded(package, value, seen):
                return True
            continue
        dependency = dependency.rstrip("?")
        for entry in package["dependencies"]:
            name = entry["rename"] or entry["name"]
            if name == dependency and entry["name"] in packages:
                if reaches_excluded(packages[entry["name"]], dependency_feature, seen):
                    return True
    return False


print(
    ",".join(
        f"{name}/{feature}"
        for name, package in sorted(packages.items())
        for feature in sorted(package["features"])
        if feature != "default" and not reaches_excluded(package, feature, set())
    )
)
