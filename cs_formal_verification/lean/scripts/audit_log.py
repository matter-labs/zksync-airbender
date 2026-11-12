#!/usr/bin/env python3
"""The messages Lake logged for one audit file (`VERIFY_AUDITS=replay` in verify.sh).

  scripts/audit_log.py <lake build log> <test/Checks/X.lean>

Prints the text of every message Lake reported for that file (built in this run, or replayed from its trace: the
same messages the `.olean` was built with), one message per block, without Lake's `info: <file>:<line>:<col>: `
prefix: the text `lake env lean <file>` prints. A message runs until the next message or Lake status line.
"""

import re
import sys

START = re.compile(r"^(info|warning|error|trace): |^[✔⚠ℹ✖] \[\d+/\d+\]|^Build completed|^Some required targets")


def main() -> int:
    log, path = sys.argv[1], sys.argv[2]
    prefix = re.compile(rf"^info: {re.escape(path)}:\d+:\d+: ")
    out: list[str] = []
    keep = False
    for line in open(log, encoding="utf-8", errors="replace").read().splitlines():
        if START.match(line):
            keep = bool(prefix.match(line))
            if keep:
                out.append(prefix.sub("", line))
        elif keep:
            out.append(line)
    print("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main())
