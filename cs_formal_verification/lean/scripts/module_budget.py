#!/usr/bin/env python3
"""Module build budget (docs/shared/lean-strategies.md 2): every module of ours compiles in at most 30 s of CPU.

The metric is the CPU time (user + sys) of the module's `lean` process, compiled alone with its imports built.
Not wall time: wall time under parallel load is off by 2-4x, and a module that elaborates in parallel can finish
in less wall time than it costs. CPU time barely depends on load; what remains (threads on efficiency cores, shared
caches) only inflates it, so a module under budget under load is under budget alone.

Three stages, each paying only for what the previous one could not settle:
  1. `build <lake build args>`: runs `lake build` while sampling (ps, every 0.5 s) the CPU time of each `lean`
     process compiling one of our files. Free: the build runs anyway.
  2. `check`: every module of the verify.sh targets (import closure of the lakefile's libraries) is looked up in
     a ledger keyed by (module, Lake input hash `depHash`). The input hash covers the source and every import, so
     an entry is valid exactly as long as Lake would not rebuild the module. A module without an entry (restored
     from Lake's artifact cache, or built outside verify.sh) is compiled again outside Lake, several at a time,
     with exact CPU from wait4.
  3. A module over budget in 1 or 2 is compiled again alone, up to twice; the minimum is its time. Over budget
     alone fails the check.
The ledger is shared by the worktrees that share Lake's artifact cache (next to it, never inside), so a module
is measured once per input hash on this machine. Without the cache (or with the ledger lost) stage 2 measures
every module once: about a cold build's CPU.

Usage (from cs_formal_verification/lean; verify.sh runs both):
  scripts/module_budget.py build CleanCore Human Slop
  scripts/module_budget.py check [--jobs N] [--table FILE]
  scripts/module_budget.py time <Module>...   (one module alone, no ledger: before/after a change)
Environment: MODULE_BUDGET_S (default 30), MODULE_BUDGET_LEDGER (ledger path), MODULE_BUDGET_JOBS (default 4).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC_DIRS = ("human", "slop", "test")
BUILD = ROOT / ".lake" / "build"
BUDGET = float(os.environ.get("MODULE_BUDGET_S", "30"))


def ledger_path() -> Path:
    if p := os.environ.get("MODULE_BUDGET_LEDGER"):
        return Path(p)
    cache = os.environ.get("LAKE_CACHE_DIR")
    if cache and os.environ.get("LAKE_ARTIFACT_CACHE", "").lower() in ("1", "true"):
        c = Path(cache.rstrip("/"))
        return c.parent / (c.name + ".module-cpu.tsv")
    return ROOT / ".lake" / "module-cpu.tsv"


def ledger_append(rows: list[tuple[str, str, float, str]]) -> None:
    """One short line per write with O_APPEND: concurrent writers (two build slots) do not interleave."""
    p = ledger_path()
    p.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(p, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o644)
    try:
        for mod, h, cpu, how in rows:
            os.write(fd, f"{mod}\t{h}\t{cpu:.1f}\t{how}\t{int(time.time())}\n".encode())
    finally:
        os.close(fd)


def ledger_read() -> dict[tuple[str, str], dict[str, list[float]]]:
    out: dict[tuple[str, str], dict[str, list[float]]] = {}
    p = ledger_path()
    if not p.exists():
        return out
    for line in p.read_text().splitlines():
        f = line.split("\t")
        if len(f) < 4:
            continue
        try:
            out.setdefault((f[0], f[1]), {}).setdefault(f[3], []).append(float(f[2]))
        except ValueError:
            continue
    return out


def src_of(mod: str) -> Path | None:
    rel = Path(*mod.split(".")).with_suffix(".lean")
    for d in SRC_DIRS:
        if (ROOT / d / rel).exists():
            return ROOT / d / rel
    return None


def mod_of(path: Path) -> str | None:
    try:
        rel = path.resolve().relative_to(ROOT)
    except ValueError:
        return None
    if rel.parts[0] not in SRC_DIRS or rel.suffix != ".lean":
        return None
    return ".".join(rel.with_suffix("").parts[1:])


IMPORT = re.compile(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", re.M)


def targets() -> list[str]:
    """Modules of verify.sh's targets: the lakefile's libraries (globs, else roots) and executable, closed under
    imports of our own files."""
    cfg = tomllib.loads((ROOT / "lakefile.toml").read_text())
    every = sorted(m for d in SRC_DIRS for p in (ROOT / d).rglob("*.lean") if (m := mod_of(p)))
    seeds: set[str] = set()
    for lib in cfg.get("lean_lib", []):
        # Lake builds a library's globs; its roots only when it has no globs
        for g in lib.get("globs", lib.get("roots", [lib["name"]])):
            if g.endswith(".+"):
                seeds.update(m for m in every if m.startswith(g[:-2] + "."))
            elif g.endswith(".*"):
                seeds.update(m for m in every if m == g[:-2] or m.startswith(g[:-2] + "."))
            else:
                seeds.add(g)
    for exe in cfg.get("lean_exe", []):
        seeds.add(exe["root"])
    seen: set[str] = set()
    todo = [m for m in seeds if src_of(m)]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        for i in IMPORT.findall(src_of(m).read_text()):
            if i not in seen and src_of(i):
                todo.append(i)
    return sorted(seen)


def dep_hash(mod: str) -> str | None:
    t = BUILD / "lib" / "lean" / Path(*mod.split(".")).with_suffix(".trace")
    try:
        return json.loads(t.read_text())["depHash"]
    except (OSError, ValueError, KeyError):
        return None


# ---------------------------------------------------------------- stage 1: sample the build


def cpu_secs(t: str) -> float:
    d = 0
    if "-" in t:
        dd, t = t.split("-", 1)
        d = int(dd)
    s = 0.0
    for x in t.split(":"):
        s = s * 60 + float(x)
    return d * 86400 + s


def sample(stop: threading.Event, seen: dict[str, float]) -> None:
    roots = tuple(str(ROOT / d) + "/" for d in SRC_DIRS)
    while not stop.is_set():
        try:
            ps = subprocess.run(["ps", "-axo", "time=,command="], capture_output=True, text=True).stdout
        except OSError:
            ps = ""
        for line in ps.splitlines():
            f = line.split()
            if len(f) < 3 or not f[1].endswith("/bin/lean"):
                continue
            src = next((a for a in f[2:] if a.endswith(".lean")), None)
            if src and src.startswith(roots):
                seen[src] = max(seen.get(src, 0.0), cpu_secs(f[0]))
        stop.wait(0.5)


def cmd_build(args: list[str]) -> int:
    seen: dict[str, float] = {}
    stop = threading.Event()
    th = threading.Thread(target=sample, args=(stop, seen), daemon=True)
    th.start()
    log = ROOT / ".lake" / f"verify-build-{args[0] if args else 'default'}.log"
    with open(log, "w") as f:
        rc = subprocess.run(["lake", "build", *args], stdout=f, stderr=subprocess.STDOUT, cwd=ROOT).returncode
    stop.set()
    th.join()
    rows = []
    for src, cpu in seen.items():
        mod = mod_of(Path(src))
        h = dep_hash(mod) if mod else None
        if mod and h:
            rows.append((mod, h, cpu, "build"))
    if rows:
        ledger_append(rows)
    tail = log.read_text().splitlines()[-1:] or [""]
    print(tail[0])
    print(f"budget: {len(rows)} modules compiled and timed (log: {log.relative_to(ROOT)})")
    if rc != 0:
        print("\n".join(l for l in log.read_text().splitlines() if "error" in l)[-4000:])
    return rc


# ---------------------------------------------------------------- stages 2 and 3: measure outside Lake


def lean_env() -> tuple[str, dict[str, str]]:
    out = subprocess.run(["lake", "env", "printenv"], capture_output=True, text=True, cwd=ROOT, check=True).stdout
    env = dict(os.environ)
    for line in out.splitlines():
        k, _, v = line.partition("=")
        if k in ("LEAN_PATH", "LEAN_SYSROOT", "PATH", "LEAN", "LAKE", "LAKE_HOME", "DYLD_LIBRARY_PATH"):
            env[k] = v
    lean = shutil.which("lean", path=env["PATH"]) or "lean"
    return lean, env


def compile_alone(mod: str, lean: str, env: dict[str, str], tmp: Path) -> tuple[float, int, str]:
    """Compile like Lake does (olean, ilean and C outputs, into a scratch dir). Returns (CPU s, exit code, output)."""
    o = tmp / mod
    args = [lean, str(src_of(mod)), "-o", f"{o}.olean", "-i", f"{o}.ilean", "-c", f"{o}.c"]
    p = subprocess.Popen(args, cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out_chunks: list[bytes] = []
    reader = threading.Thread(target=lambda: out_chunks.append(p.stdout.read()), daemon=True)
    reader.start()
    _, status, ru = os.wait4(p.pid, 0)
    reader.join()
    p.returncode = os.waitstatus_to_exitcode(status)
    for ext in (".olean", ".ilean", ".c"):
        try:
            os.unlink(f"{o}{ext}")
        except OSError:
            pass
    return ru.ru_utime + ru.ru_stime, p.returncode, b"".join(out_chunks).decode(errors="replace")


def verdict(entries: dict[str, list[float]]) -> tuple[float, str]:
    if "alone" in entries:
        return min(entries["alone"]), "alone"
    best = min((min(v), k) for k, v in entries.items())
    return best


def cmd_check(jobs: int, table: Path | None) -> int:
    mods = targets()
    hashes = {m: dep_hash(m) for m in mods}
    unbuilt = [m for m, h in hashes.items() if h is None]
    if unbuilt:
        print(f"budget: FAIL {len(unbuilt)} target modules have no build trace (build first): {unbuilt[:5]}")
        return 1
    led = ledger_read()
    missing = [m for m in mods if (m, hashes[m]) not in led]
    lean, env = lean_env()
    tmp = Path(tempfile.mkdtemp(prefix="module-budget-"))
    failed: list[str] = []
    try:
        if missing:
            print(f"budget: measuring {len(missing)} modules not in the ledger ({jobs} at a time)", flush=True)
            lock = threading.Lock()
            queue = list(missing)
            done = [0]

            def worker() -> None:
                while True:
                    with lock:
                        if not queue:
                            return
                        m = queue.pop(0)
                    cpu, rc, out = compile_alone(m, lean, env, tmp)
                    with lock:
                        done[0] += 1
                        if rc != 0:
                            failed.append(m)
                            print(f"budget: {m} failed to compile:\n{out[-2000:]}", flush=True)
                            continue
                        ledger_append([(m, hashes[m], cpu, "par" if jobs > 1 else "alone")])
                        led.setdefault((m, hashes[m]), {}).setdefault("par" if jobs > 1 else "alone", []).append(cpu)
                        if done[0] % 50 == 0:
                            print(f"budget: {done[0]}/{len(missing)}", flush=True)

            ths = [threading.Thread(target=worker) for _ in range(max(1, jobs))]
            for t in ths:
                t.start()
            for t in ths:
                t.join()
        if failed:
            print(f"budget: FAIL {len(failed)} modules did not compile outside Lake")
            return 1
        # stage 3: anything over budget that was not timed alone, alone, up to twice
        for m in mods:
            for _ in range(2):
                cpu, how = verdict(led[(m, hashes[m])])
                if cpu <= BUDGET or (how == "alone" and len(led[(m, hashes[m])]["alone"]) >= 2):
                    break
                print(f"budget: re-timing {m} alone ({cpu:.1f} s {how})", flush=True)
                c, rc, out = compile_alone(m, lean, env, tmp)
                if rc != 0:
                    print(f"budget: {m} failed to compile:\n{out[-2000:]}")
                    return 1
                ledger_append([(m, hashes[m], c, "alone")])
                led[(m, hashes[m])].setdefault("alone", []).append(c)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    rows = sorted(((verdict(led[(m, hashes[m])]), m) for m in mods), reverse=True)
    if table:
        with open(table, "w") as f:
            f.write("module\tcpu_s\tmeasured\n")
            for (cpu, how), m in rows:
                f.write(f"{m}\t{cpu:.1f}\t{how}\n")
    over = [(c, m) for (c, _), m in rows if c > BUDGET]
    n15 = sum(1 for (c, _), _ in rows if c > 15)
    n10 = sum(1 for (c, _), _ in rows if c > 10)
    top = ", ".join(f"{m} {c:.1f}" for (c, _), m in rows[:3])
    print(f"budget: {len(mods)} modules, CPU > 10 s: {n10}, > 15 s: {n15}, > {BUDGET:g} s: {len(over)}; top: {top}")
    if over:
        for c, m in over:
            print(f"  over budget: {m} {c:.1f} s CPU alone")
        print(f"budget: FAIL {len(over)} modules over {BUDGET:g} s (lean-strategies.md 2: restructure, do not raise)")
        return 1
    return 0


def cmd_time(mods: list[str]) -> int:
    """Time modules alone (imports must be built), without the ledger: for profiling a change."""
    lean, env = lean_env()
    tmp = Path(tempfile.mkdtemp(prefix="module-budget-"))
    rc = 0
    try:
        for m in mods:
            if src_of(m) is None:
                print(f"{m}: no such module")
                rc = 1
                continue
            cpu, r, out = compile_alone(m, lean, env, tmp)
            if r != 0:
                print(out[-3000:])
                rc = 1
            print(f"{m}\t{cpu:.1f} s CPU" + ("" if r == 0 else " (FAILED)"), flush=True)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return rc


def main() -> int:
    if len(sys.argv) > 1 and sys.argv[1] == "build":
        return cmd_build(sys.argv[2:])
    if len(sys.argv) > 1 and sys.argv[1] == "time":
        return cmd_time(sys.argv[2:])
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["check"])
    ap.add_argument("--jobs", type=int, default=int(os.environ.get("MODULE_BUDGET_JOBS", "4")))
    ap.add_argument("--table", type=Path, default=ROOT / ".lake" / "module-budget.tsv")
    a = ap.parse_args()
    return cmd_check(a.jobs, a.table)


if __name__ == "__main__":
    sys.exit(main())
