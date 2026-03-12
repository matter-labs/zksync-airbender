#!/usr/bin/env python3
"""Read Cargo JSON messages from stdin and print test executables or run commands."""

from __future__ import annotations

import argparse
import json
import shlex
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
        "--lock-cmd",
        default=".agents/bin/with_gpu_lock.sh",
        help="Lock wrapper command to prefix when printing run commands.",
    )
    return parser.parse_args()


def format_output(args: argparse.Namespace, executable: str) -> str:
    if not args.print_run_command:
        return executable

    command = [args.lock_cmd, executable]
    if args.test_name:
        command.extend(["--exact", args.test_name, "--nocapture"])

    return shlex.join(command)


def main() -> int:
    args = parse_args()
    seen: set[str] = set()

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
        print(format_output(args, executable))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
