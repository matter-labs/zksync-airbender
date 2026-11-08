#!/usr/bin/env python3
"""Convert our Lean files to the module system (Lean 4.34 `module`), as far as the import graph allows.

Deterministic and re-runnable (idempotent): run it after every rebase and after each Sail-stripping step.

A file becomes a module when every import is module-compatible: Lean core, a dependency whose source starts
with `module` (Mathlib, Batteries, ...), or one of our files that is (or becomes) a module. A module cannot
import a non-module (`cannot import non-module`), so a file that reaches the Sail model, lean-sail or Clean
(none of which are modules) stays a non-module leaf; non-modules may import modules. `KEEP` lists files kept
non-module by hand, each with its reason.

Per converted file:
  * `module` before the imports (after any leading comment);
  * `import X` -> `public import X` (visibility unchanged; narrow later with `lake shake`);
  * `@[expose] public section` after the imports: every declaration stays public with its body visible, so
    `decide`, `rfl` and `simp [f]` across files keep working (pitfall: non-exposed bodies are opaque downstream);
  * `theorem ... := rfl` -> `:= by rfl`: a term-mode proof of an exported theorem is elaborated in the
    exported view, where private and non-exposed definitions do not unfold; `by` proofs are not.

Usage: scripts/modulize.py [--dry-run] [--quiet]   (from cs_formal_verification/lean)
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC_DIRS = ("human", "slop", "test")
# Roots shipped with the toolchain; all are modules since Lean 4.22.
CORE_ROOTS = {"Init", "Std", "Lean", "Lake"}
# Files kept non-module by hand: module name -> reason. Their importers stay non-module too.
KEEP: dict[str, str] = {}
# Files whose proofs evaluate concrete data in the kernel (`decide`, `decide +kernel`, `with_unfolding_all`) through
# Init definitions that Init does not expose to modules: each privately imports exactly the Init modules it needs
# with `import all` (bodies visible to this file's proofs only; importers and statements unchanged). Sets measured
# per file (elaboration time as the non-module baseline). Module name -> Init modules.
UNTIL_435 = "-- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)"
REPR = "-- Init.Data.Repr is not exposed (still true in 4.35)"
IMPORT_ALL_COMMENT = {"Init.Data.Array.Basic": UNTIL_435, "Init.Data.Array.DecidableEq": UNTIL_435,
                      "Init.Data.Vector.Basic": UNTIL_435, "Init.Data.Repr": REPR, "Init.Data.String.Defs": REPR}
_A, _D, _V, _R, _S = ("Init.Data.Array.Basic", "Init.Data.Array.DecidableEq", "Init.Data.Vector.Basic",
                      "Init.Data.Repr", "Init.Data.String.Defs")
IMPORT_ALL: dict[str, tuple[str, ...]] = {
    "Slop.KeccakSplit.Reference.CallReference": (_A,),
    "Slop.Lookups": (_A,),
    "Slop.ShiftBinop.ArtifactChecks": (_R,),
    "Slop.Deleg.Vectors": (_D, _V),
    "Slop.Blake2G.ArtifactChecks": (_D, _V),
    "Slop.Keccak.ArtifactChecks": (_D, _V),
    "Slop.KeccakSplit.Memory.Order": (_D, _V),
    "Tests.Blake2Compression": (_D, _V),
    "Tests.KeccakFixedTables": (_D, _V),
    "Slop.KeccakSplit.Setup.ColumnParity.Rows": (_D,),
    "Slop.Bigint.ArtifactChecks": (_D, _V, _R),
    "Slop.Blake2Round.ArtifactChecks": (_D, _V, _R, _S),
    # found once the files above became modules (smallest passing set, measured the same way)
    "Slop.Keccak.CallPorts": (_A,),
    "Slop.KeccakSplit.ThetaRho.Lanes": (_A,),
    "Slop.UnifiedReduced.RV.ControlLookups": (_A,),
    "Slop.Delegation.Memory": (_D,),
    "Slop.KeccakSplit.Memory.History": (_D,),
    "Slop.Blake2Round.RVSpec": (_D, _V),
    "Tests.Branch": (_A,),
    "Tests.Comparison": (_A,),
    "Tests.Division": (_A,),
    "Tests.MulDiv": (_A,),
    "Tests.KeccakController": (_D, _V),
    "Tests.ShiftBinop": (_D, _V),
    "Tests.Shifts": (_D, _V),
    "Tests.TraceROM": (_D, _V),
    "Slop.Keccak.StateCells": (_A,),
    "Slop.UnifiedReduced.RV.ControlResolution": (_A,),
    "Tests.Blake2GMemory": (_A,),
    "Tests.Bigint": (_D, _V),
    "Tests.BigintMemory": (_D, _V),
    "Tests.BigintMultiplication": (_D, _V),
    "Tests.Blake2G": (_D, _V),
    "Tests.ShiftBinopImmediate": (_D, _V),
    "Tests.ShiftBinopPorts": (_D, _V),
    "Slop.Keccak.Phases.Mix": (_A,),
    "Slop.Keccak.RVSpec": (_A,),
    "Slop.KeccakSplit.RVStep": (_A,),
    "Slop.UnifiedReduced.RV.ControlMembership": (_A,),
    "Slop.KeccakSplit.Reference.CallSteps": (_A,),
    "Slop.Keccak.PhaseSteps": (_A,),
    "Slop.KeccakSplit.Chain.Calls": (_A,),
    "Tests.DelegationMemory": (_A,),
    "Tests.KeccakChi": (_A,),
    "Tests.KeccakIota": (_A,),
    "Tests.KeccakMix": (_A,),
    "Tests.KeccakRho": (_A,),
    "Tests.DelegationROMBoundary": (_D, _V),
    "Tests.Keccak": (_D, _V),
    "Tests.UnifiedDelegation": (_D, _V),
}
# Generated proof families: every file under the prefix gets the same set.
IMPORT_ALL_PREFIX: dict[str, tuple[str, ...]] = {}


def import_all_for(module: str) -> tuple[str, ...]:
    if module in IMPORT_ALL:
        return IMPORT_ALL[module]
    return next((mods for prefix, mods in IMPORT_ALL_PREFIX.items() if module.startswith(prefix)), ())


# Files that run code at elaboration time (command/term/tactic elaborators, attribute registration): their
# imports are also `meta` imports and the body is a `public meta section` (meta code may call only meta code or
# definitions from `meta import`ed modules). Detected by META_RE.
META_RE = re.compile(r"^\s*(?:elab|run_cmd|run_elab|run_meta|declare_syntax_cat)\b"
                     r"|@\[(?:command_elab|term_elab|tactic)\b", re.M)
# Files that `#eval` code using imported definitions: the interpreter needs their compiled code, which a module only
# gets through `meta import`; such files also `public meta import` each import (their own definitions stay ordinary).
EVAL_RE = re.compile(r"^#eval\b", re.M)

IMPORT_RE = re.compile(r"^(?P<mods>(?:public\s+|meta\s+)*)import\s+(?P<all>all\s+)?(?P<name>[\w.'«»]+)\s*(?P<rest>--.*)?$")
DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*"
                     r"(?P<kw>theorem|lemma|def|abbrev|instance|example|structure|inductive|class|opaque|axiom)\b")


def strip_leading_comments(lines: list[str]) -> int:
    """Index of the first line that is not blank or part of a leading comment."""
    i, depth = 0, 0
    while i < len(lines):
        line = lines[i]
        if depth:
            depth += line.count("/-") - line.count("-/")
            i += 1
            continue
        s = line.strip()
        if not s or s.startswith("--"):
            i += 1
            continue
        if s.startswith("/-") and not s.startswith("/-!"):
            depth = s.count("/-") - s.count("-/")
            i += 1
            continue
        break
    return i


class Source:
    def __init__(self, module: str, path: Path):
        self.module, self.path = module, path
        self.text = path.read_text(encoding="utf-8")
        self.lines = self.text.split("\n")
        start = strip_leading_comments(self.lines)
        self.is_module = start < len(self.lines) and self.lines[start].strip() == "module"
        self.imports: list[str] = []
        for line in self.lines[start:]:
            s = line.strip()
            if not s or s == "module" or s.startswith("--"):
                continue
            m = IMPORT_RE.match(s)
            if not m:
                break
            self.imports.append(m.group("name"))


def our_sources() -> dict[str, Source]:
    sources = {}
    for src in SRC_DIRS:
        base = ROOT / src
        for path in sorted(base.rglob("*.lean")):
            module = ".".join(path.relative_to(base).with_suffix("").parts)
            sources[module] = Source(module, path)
    return sources


def external_roots() -> list[Path]:
    roots = [p for p in (ROOT / ".lake/packages").glob("*") if p.is_dir()]
    sail = ROOT / "sail-rv32"
    return roots + [sail, sail / "lean-sail"]


_external_cache: dict[str, bool] = {}


def external_is_module(name: str) -> bool:
    """A dependency module is module-compatible iff its source starts with `module`."""
    if name in _external_cache:
        return _external_cache[name]
    result = False
    if name.split(".")[0] in CORE_ROOTS:
        result = True
    else:
        rel = Path(*name.split(".")).with_suffix(".lean")
        for root in external_roots():
            path = root / rel
            if path.is_file():
                lines = path.read_text(encoding="utf-8").split("\n")
                i = strip_leading_comments(lines)
                result = i < len(lines) and lines[i].split("--")[0].strip() == "module"
                break
    _external_cache[name] = result
    return result


TOP_DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?P<mods>(?:(?:private|protected|noncomputable|nonrec|unsafe|partial|local|scoped)\s+)*)"
                         r"(?P<kw>theorem|lemma|def|abbrev|instance|structure|inductive|class|example)\b\s*(?P<name>[^\s:({\[]*)")


def leaked_private(source: Source, seed: frozenset[str] = frozenset()) -> set[str]:
    """Private declarations that a module could not keep private: in a module a public signature or an exposed
    (`@[expose]`) definition body cannot mention a `private` declaration (a non-module can). Over-approximates
    (a binder with the same name also counts); making a declaration public changes no meaning."""
    blocks: list[tuple[bool, str, str, list[str]]] = []  # (private, kind, name, lines)
    for line in source.lines:
        m = TOP_DECL_RE.match(line)
        if m:
            blocks.append(("private" in m.group("mods"), m.group("kw"), m.group("name"), [line]))
        elif blocks and blocks[-1][1] and not re.match(r"^(namespace|end|section|open|variable|universe|/-|--)\b", line):
            blocks[-1][3].append(line)
        else:
            blocks.append((True, "", "", []))  # a boundary
    private = {name.split(".")[-1] for priv, kind, name, _ in blocks if priv and name}
    if not private:
        return set()
    pattern = re.compile(r"(?<![\w.'])(" + "|".join(re.escape(n) for n in sorted(private)) + r")(?![\w'])")
    # `seed`: private names another file reaches with `open private ... from` (a module cannot). Iterate to a
    # fixpoint: a private declaration made public exposes the private names its own signature/body mentions.
    leaked: set[str] = set(seed) & private
    while True:
        before = len(leaked)
        for priv, kind, name, lines in blocks:
            if not kind or (priv and name.split(".")[-1] not in leaked):
                continue
            text = "\n".join(lines)
            if kind in ("theorem", "lemma"):
                # the proof starts at `:= by` or a line-final `:=` (a `let x := ...` may sit in the statement)
                proof = re.search(r":=\s*by\b|:=\s*$|^\s*\|", text, flags=re.M)
                text = text[:proof.start()] if proof else re.split(r":=|\bwhere\b", text, maxsplit=1)[0]
            text = text.split(name, 1)[1] if name and name in text else text
            leaked |= set(pattern.findall(text))
        if len(leaked) == before:
            break
    # Generalized field notation (`c.f` for a `private def T.f`) does not find a private name in a module.
    dotted = {name.split(".")[-1] for priv, kind, name, _ in blocks if priv and "." in name}
    leaked |= {n for n in dotted if re.search(r"[\w)\]]\." + re.escape(n) + r"(?![\w'])", source.text)}
    return leaked


def unprivate(lines: list[str], names: set[str]) -> list[str]:
    out = []
    for line in lines:
        m = TOP_DECL_RE.match(line)
        if m and "private" in m.group("mods") and m.group("name").split(".")[-1] in names:
            line = re.sub(r"\bprivate\s+", "", line, count=1)
        out.append(line)
    return out


def blockers(sources: dict[str, Source]) -> dict[str, str | None]:
    """For each of our files: None if it can be a module, else the non-module import chain that blocks it."""
    memo: dict[str, str | None] = {}

    def visit(module: str, stack: tuple[str, ...]) -> str | None:
        if module in memo:
            return memo[module]
        if module in KEEP:
            memo[module] = f"kept: {KEEP[module]}"
            return memo[module]
        memo[module] = None  # cycles cannot occur in Lean; guard anyway
        for imp in sources[module].imports:
            if imp in sources:
                below = visit(imp, stack + (module,))
                if below is not None:
                    memo[module] = f"{imp} -> {below}"
                    return memo[module]
            elif not external_is_module(imp):
                memo[module] = imp
                return imp
        return None

    for module in sources:
        visit(module, ())
    return memo


def root_cause(chain: str) -> str:
    return chain.split(" -> ")[-1]


MODULES: set[str] = set()  # the files that are (or become) modules, set by main


def convert(source: Source, seed: frozenset[str] = frozenset()) -> str:
    meta = bool(META_RE.search(source.text))
    meta_imports = meta or bool(EVAL_RE.search(source.text))
    lines = list(source.lines)
    start = strip_leading_comments(lines)
    out = lines[:start] + ["module"]
    i = start
    last_import = None
    body: list[str] = []
    # header: imports (and blank/comment lines between them)
    while i < len(lines):
        s = lines[i].strip()
        m = IMPORT_RE.match(s)
        if m:
            mods = m.group("mods") or ""
            stmt = lines[i].strip()
            if "public" not in mods:
                stmt = "public " + stmt
            out.append(stmt)
            if meta_imports and "meta" not in mods:
                out.append(stmt.replace("public import", "public meta import", 1))
            last_import = len(out)
            i += 1
        elif not s or s.startswith("--"):
            out.append(lines[i])
            i += 1
        else:
            break
    if last_import is None:
        last_import = len(out)
    if import_all_for(source.module):
        added = [f"import all {m} {IMPORT_ALL_COMMENT[m]}" for m in import_all_for(source.module)]
        out[last_import:last_import] = added
        last_import += len(added)
    # trailing blanks/comments after the last import belong to the body
    tail = out[last_import:]
    section = "public meta section" if meta else "@[expose] public section"
    out = out[:last_import] + ["", section] + ([""] if tail and tail[0].strip() else []) + tail
    body = lines[i:]
    if not meta:
        body = unprivate(body, leaked_private(source, seed))
    # `open private X from M` cannot reach M's private names in a module; M (converted too) makes X public, and
    # the opener resolves X by its namespace (a target outside the module set keeps the line and fails loudly).
    body = [line for line in body
            if not ((m := re.match(r"^\s*open private .+ from (\S+)\s*$", line)) and m.group(1) in MODULES)]
    out += rewrite_rfl(body)
    return "\n".join(out)


def rewrite_rfl(body: list[str]) -> list[str]:
    """`:= rfl` ending a theorem/lemma (same line or next line) -> `:= by rfl`."""
    out = list(body)
    kind = None
    for k, line in enumerate(out):
        m = DECL_RE.match(line)
        if m:
            kind = m.group("kw")
        if kind not in ("theorem", "lemma"):
            continue
        if re.search(r":=\s*rfl\s*$", line):
            out[k] = re.sub(r":=\s*rfl\s*$", ":= by rfl", line)
        elif re.match(r"^\s+rfl\s*$", line) and k > 0 and re.search(r":=\s*$", out[k - 1]):
            out[k] = line.replace("rfl", "by rfl", 1)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dry-run", action="store_true", help="report only, change nothing")
    ap.add_argument("--quiet", action="store_true", help="do not list the non-module files")
    args = ap.parse_args()

    sources = our_sources()
    block = blockers(sources)
    modules = sorted(m for m in sources if block[m] is None)
    stay = sorted(m for m in sources if block[m] is not None)
    broken = [m for m in stay if sources[m].is_module]
    MODULES.update(modules)
    opened: dict[str, set[str]] = {}
    for module in modules:
        for names, target in re.findall(r"^\s*open private ([^\n]+?) from (\S+)\s*$", sources[module].text, re.M):
            opened.setdefault(target, set()).update(names.split())
    converted = 0
    for module in modules:
        source = sources[module]
        if source.is_module:
            continue
        converted += 1
        if not args.dry_run:
            source.path.write_text(convert(source, frozenset(opened.get(module, ()))), encoding="utf-8")

    print(f"files: {len(sources)}; modules: {len(modules)} ({converted} converted now); non-module: {len(stay)}")
    causes: dict[str, int] = {}
    for m in stay:
        causes[root_cause(block[m])] = causes.get(root_cause(block[m]), 0) + 1
    for cause, n in sorted(causes.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"  non-module because of {cause}: {n}")
    if not args.quiet:
        for m in stay:
            print(f"NON-MODULE {m}: {block[m]}")
    if broken:
        print("ERROR: modules that now import a non-module (undo their conversion or fix the import):")
        for m in broken:
            print(f"  {m}: {block[m]}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
