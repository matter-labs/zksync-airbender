#!/usr/bin/env python3
"""No warnings in our code: verify.sh fails on any warning (or error) that Lean or Lake reports for one of our modules
(human/, proven/, test/: every module of verify.sh's targets, scripts/module_budget.py `targets()`). Warnings in the
dependencies (Mathlib, Clean, lean-sail) and in the generated Sail model are not ours and not checked (README "No
warnings").

Where the messages come from, per module:
  1. Lake's trace of the module (`.lake/build/lib/lean/<Module>.trace`, field `log`): the messages Lean printed when
     Lake compiled it. Lake keeps them across runs (a replayed module shows them again), so a module compiled by an
     earlier build is checked as well.
  2. A module restored from Lake's artifact cache has a synthetic trace without messages. It passes if the warnings
     ledger (beside module_budget.py's CPU ledger, keyed the same way by module and Lake input hash) records it as
     compiled without warnings; otherwise it is compiled again outside Lake (like module_budget.py stage 2) and, when
     clean, recorded.
  3. Lake's own warnings about our files are in no trace (e.g. a non-module file importing a package that requires the
     module system): read from the `lake build` logs given on the command line.

Usage (from cs_formal_verification/lean; verify.sh runs it after the build and the budget check):
  scripts/no_warnings.py [BUILD_LOG...]
Environment: MODULE_BUDGET_JOBS (modules compiled at once, default 4), MODULE_BUDGET_LEDGER (as module_budget.py).
"""

from __future__ import annotations

import json
import os
import re
import shutil
import sys
import tempfile
import threading
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import module_budget as mb  # noqa: E402

# Lake's console form of a message about one of our files: `warning: proven/Proven/X.lean[:l:c]: ...`
LAKE_MESSAGE = re.compile(r"^(?:warning|error): ((?:human|proven|test)/\S+?\.lean[:\s].*)$")


def trace_messages(mod: str) -> tuple[str | None, list[str] | None]:
    """(Lake input hash, the module's warnings and errors); messages None when the trace has none to give (restored
    from the artifact cache); hash None when the module has no trace (not built)."""
    t = mb.BUILD / "lib" / "lean" / Path(*mod.split(".")).with_suffix(".trace")
    try:
        d = json.loads(t.read_text())
    except (OSError, ValueError):
        return None, None
    log = d.get("log") or []
    if d.get("synthetic") and not log:
        return d.get("depHash"), None
    return d.get("depHash"), [e["message"].split("\n", 1)[0] for e in log if e.get("level") in ("warning", "error")]


def main(logs: list[str]) -> int:
    mods = mb.targets()
    found: dict[str, None] = {}  # messages, in order, without duplicates
    unbuilt: list[str] = []
    restored: list[tuple[str, str]] = []
    from_traces = 0
    for m in mods:
        h, msgs = trace_messages(m)
        if h is None:
            unbuilt.append(m)
        elif msgs is None:
            restored.append((m, h))
        else:
            from_traces += 1
            found.update(dict.fromkeys(msgs))
    if unbuilt:
        print(f"warnings: FAIL {len(unbuilt)} target modules have no build trace (build first): {unbuilt[:5]}")
        return 1

    clean = mb.warnings_ledger_read()
    to_compile = [(m, h) for m, h in restored if (m, h) not in clean]
    if to_compile:
        jobs = max(1, int(os.environ.get("MODULE_BUDGET_JOBS", "4")))
        print(f"warnings: compiling {len(to_compile)} modules restored from Lake's artifact cache ({jobs} at a time)",
              flush=True)
        lean, env = mb.lean_env()
        tmp = Path(tempfile.mkdtemp(prefix="no-warnings-"))
        lock = threading.Lock()
        queue = list(to_compile)
        failed: list[str] = []

        def worker() -> None:
            while True:
                with lock:
                    if not queue:
                        return
                    m, h = queue.pop(0)
                _, rc, out = mb.compile_alone(m, lean, env, tmp)
                msgs = mb.output_warnings(out)
                with lock:
                    if rc != 0:
                        failed.append(m)
                        print(f"warnings: {m} failed to compile:\n{out[-2000:]}", flush=True)
                    elif msgs:
                        found.update(dict.fromkeys(msgs))
                    else:
                        mb.warnings_ledger_append([(m, h)])

        try:
            threads = [threading.Thread(target=worker) for _ in range(jobs)]
            for t in threads:
                t.start()
            for t in threads:
                t.join()
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
        if failed:
            print(f"warnings: FAIL {len(failed)} modules did not compile outside Lake")
            return 1

    for log in logs:
        try:
            text = Path(log).read_text(errors="replace")
        except OSError:
            print(f"warnings: FAIL cannot read build log {log}")
            return 1
        for line in text.splitlines():
            if mm := LAKE_MESSAGE.match(line):
                found.setdefault(mm.group(1))

    # Lake prints a message it replays from a trace too: count each once
    msgs = list(found)
    print(f"warnings: {len(mods)} modules ({from_traces} from Lake's traces, {len(restored)} restored from the "
          f"artifact cache: {len(restored) - len(to_compile)} from the ledger, {len(to_compile)} compiled); "
          f"{len(logs)} build logs")
    if msgs:
        files = sorted({re.split(r"[:\s]", x, maxsplit=1)[0] for x in msgs})
        for x in msgs[:60]:
            print(f"  {x[:240]}")
        if len(msgs) > 60:
            print(f"  ... {len(msgs) - 60} more")
        print(f"warnings: FAIL {len(msgs)} warnings in {len(files)} files of ours (fix them; README \"No warnings\")")
        return 1
    print("warnings: none in our code")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
