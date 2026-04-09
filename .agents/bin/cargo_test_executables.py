#!/usr/bin/env python3
"""Read Cargo JSON messages from stdin and print test executables or run commands."""

from __future__ import annotations

import argparse
import json
import shlex
import subprocess
import sys


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--print-run-command",
        action="store_true",
        help="Print a locked test invocation instead of only the executable path.",
    )
    parser.add_argument(
        "--test-name",
        help="Optional exact test name to append as '--exact <name> --nocapture'.",
    )
    parser.add_argument(
        "--test-arg",
        action="append",
        default=[],
        metavar="ARG",
        help="Extra libtest runner arg to append when printing run commands.",
    )
    parser.add_argument(
        "--lock-cmd",
        default=".agents/bin/with_gpu_lock.sh",
        help="Lock wrapper command to prefix when printing run commands.",
    )
    return parser.parse_args()


def collect_executables() -> list[str]:
    seen: set[str] = set()
    executables: list[str] = []

    for raw_line in sys.stdin:
        line = raw_line.strip()
        if not line or not line.startswith("{"):
            continue

        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            continue

        executable = message.get("executable")
        profile = message.get("profile") or {}

        if not executable or not profile.get("test", False):
            continue

        if executable in seen:
            continue

        seen.add(executable)
        executables.append(executable)

    return executables


def ensure_fully_qualified_test_name(test_name: str) -> None:
    if "::" in test_name:
        return

    raise ValueError(
        f"--test-name must be the full libtest path accepted by --exact; got {test_name!r}"
    )


def list_tests(executable: str) -> set[str]:
    result = subprocess.run(
        [executable, "--list"],
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        stderr = result.stderr.strip()
        raise RuntimeError(
            f"failed to query tests from {executable!r} with --list"
            + (f": {stderr}" if stderr else "")
        )

    tests: set[str] = set()
    for raw_line in result.stdout.splitlines():
        line = raw_line.strip()
        if ": " not in line:
            continue

        name, kind = line.split(": ", 1)
        if kind in {"test", "benchmark"}:
            tests.add(name)

    return tests


def resolve_test_executable(executables: list[str], test_name: str) -> str:
    ensure_fully_qualified_test_name(test_name)

    exact_matches: list[str] = []
    suffix_matches: set[str] = set()

    for executable in executables:
        tests = list_tests(executable)
        if test_name in tests:
            exact_matches.append(executable)
            continue

        for test in tests:
            if test.endswith(f"::{test_name}") or test.endswith(test_name):
                suffix_matches.add(test)

    if len(exact_matches) == 1:
        return exact_matches[0]

    if len(exact_matches) > 1:
        matches = ", ".join(repr(match) for match in exact_matches)
        raise ValueError(f"--test-name {test_name!r} matched multiple test binaries: {matches}")

    if suffix_matches:
        rendered_matches = ", ".join(repr(match) for match in sorted(suffix_matches)[:5])
        extra = "" if len(suffix_matches) <= 5 else ", ..."
        raise ValueError(
            f"--test-name {test_name!r} is not an exact match; matching full test names: "
            f"{rendered_matches}{extra}"
        )

    raise ValueError(f"--test-name {test_name!r} was not found in the built test binaries")


def format_output(args: argparse.Namespace, executable: str) -> str:
    if not args.print_run_command:
        return executable

    command = [args.lock_cmd, executable]
    if args.test_name:
        command.extend(["--exact", args.test_name])
    command.extend(args.test_arg)
    if "--nocapture" not in args.test_arg:
        command.append("--nocapture")

    return shlex.join(command)


def main() -> int:
    try:
        args = parse_args()
        executables = collect_executables()

        if args.print_run_command and args.test_name:
            executable = resolve_test_executable(executables, args.test_name)
            print(format_output(args, executable))
            return 0

        for executable in executables:
            print(format_output(args, executable))
    except (RuntimeError, ValueError) as err:
        print(err, file=sys.stderr)
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
