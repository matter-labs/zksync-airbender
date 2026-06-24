#!/usr/bin/env python3
"""Extract total hardware PMC counts from an Instruments .trace recorded with a
"CPU Counters" instrument in "Sample by Time" mode.

Such a trace exports a `counters-profile` table whose `pmc-events` column holds,
per sample interval, a space-separated array of the configured PMU event counts
(e.g. "611 31004 0"). The per-event totals are the column-wise sums across rows.

Event names are not in the table export, so they are read from the trace's
`form.template` (the configured event list, in array order). They are classified
into `instructions` (INST_RETIRED) and `cycles` (CPU_CLK_UNHALTED / CORE_ACTIVE).

Usage:  extract_counters.py <trace> [--debug]
Prints KEY=VALUE lines incl. `instructions=`, `cycles=`, `ipc=` when identifiable.
"""
import os
import re
import subprocess
import sys
import xml.etree.ElementTree as ET


def export(trace, xpath=None, toc=False):
    cmd = ["xcrun", "xctrace", "export", "--input", trace]
    if toc:
        cmd += ["--toc"]
    if xpath:
        cmd += ["--xpath", xpath]
    return subprocess.run(cmd, capture_output=True, text=True).stdout


def event_names(trace):
    """Ordered PMU event names from the trace's form.template, if available."""
    form = os.path.join(trace, "form.template")
    if not os.path.exists(form):
        return []
    xml = subprocess.run(
        ["plutil", "-convert", "xml1", "-o", "-", form], capture_output=True, text=True
    ).stdout
    # The configured event list appears as one combined string, e.g.
    #   "INST_ALL (INST_RETIRED.ANY_P), CORE_ACTIVE_CYCLE (...), CPU_CLK_UNHALTED..."
    best = []
    for m in re.finditer(r"<string>([^<]*)</string>", xml):
        s = m.group(1)
        if "INST_RETIRED" in s and ("CLK_UNHALTED" in s or "CORE_ACTIVE" in s):
            names = [n.strip() for n in s.split(", ") if n.strip()]
            if len(names) > len(best):
                best = names
    return best


def parse_counters(trace, target="riscv_transpiler", debug=False):
    data = export(
        trace, xpath='/trace-toc/run[@number="1"]/data/table[@schema="counters-profile"]'
    )
    if not data.strip():
        return None
    root = ET.fromstring(data)
    node = root.find("node")
    if node is None:
        return None
    cols = [c.findtext("engineering-type") or "" for c in node.find("schema").findall("col")]
    try:
        pmc_col = cols.index("pmc-events")
    except ValueError:
        return None
    proc_col = cols.index("process") if "process" in cols else None

    # id -> array of ints for every <pmc-events> definition (for ref resolution).
    arrays = {}
    for e in node.iter("pmc-events"):
        eid = e.get("id")
        if eid is not None:
            arrays[eid] = [int(x) for x in (e.text or "").split()]
    # id -> process display name (so we can keep only the target process's samples;
    # "Sample by Time" counts per-core, so other processes scheduled on the core
    # would otherwise pollute the totals).
    procname = {}
    for e in node.iter("process"):
        if e.get("id") is not None:
            procname[e.get("id")] = e.get("fmt") or ""

    nrows = 0
    rows_with = 0
    skipped_other = 0
    sums = []
    for row in node.findall("row"):
        nrows += 1
        children = list(row)
        if pmc_col >= len(children):
            continue
        # Filter to the target process when we can identify it.
        if proc_col is not None and proc_col < len(children) and target:
            pc = children[proc_col]
            pid = pc.get("ref") or pc.get("id")
            name = procname.get(pid, "")
            if name and target not in name:
                skipped_other += 1
                continue
        cell = children[pmc_col]
        if cell.tag != "pmc-events":
            continue
        vals = arrays.get(cell.get("ref")) if cell.get("ref") else (
            [int(x) for x in (cell.text or "").split()]
        )
        if not vals:
            continue
        if len(vals) > len(sums):
            sums.extend([0] * (len(vals) - len(sums)))
        for i, v in enumerate(vals):
            sums[i] += v
        rows_with += 1

    return {"sums": sums, "n_rows": nrows, "rows_with": rows_with, "skipped_other": skipped_other}


def classify(names, n):
    instr = cyc = None
    for i in range(n):
        nm = (names[i] if i < len(names) else "").upper()
        if instr is None and ("INST" in nm or "RETIRED" in nm):
            instr = i
        if cyc is None and ("CYCLE" in nm or "CLK" in nm or "CORE_ACTIVE" in nm):
            cyc = i
    # Fallback to this template's known order: 0=instructions, 1=cycles.
    if instr is None and n >= 1:
        instr = 0
    if cyc is None and n >= 2:
        cyc = 1
    return instr, cyc


def main():
    debug = "--debug" in sys.argv[1:] or os.environ.get("PROFILE_DEBUG") == "1"
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if not args:
        print("usage: extract_counters.py <trace> [--debug]", file=sys.stderr)
        return 2
    trace = args[0]

    parsed = parse_counters(trace, debug)
    if not parsed or not any(parsed["sums"]):
        print("no_counter_table=1", file=sys.stderr)
        if debug:
            toc = export(trace, toc=True)
            try:
                seen = sorted({t.get("schema", "") for t in ET.fromstring(toc).iter("table")})
                print("available_schemas=" + ",".join(seen), file=sys.stderr)
            except ET.ParseError:
                pass
        return 1

    sums = parsed["sums"]
    names = event_names(trace)
    instr_i, cyc_i = classify(names, len(sums))

    if debug:
        print(
            f"# schema=counters-profile rows={parsed['n_rows']} "
            f"rows_with_counters={parsed['rows_with']}",
            file=sys.stderr,
        )
        for i, s in enumerate(sums):
            nm = names[i] if i < len(names) else f"event{i}"
            print(f"#   event[{i}] {nm!r} = {s:,}", file=sys.stderr)

    print(f"samples={parsed['rows_with']}")
    for i, s in enumerate(sums):
        nm = (names[i] if i < len(names) else f"event{i}").replace(" ", "_")
        print(f"event[{i}].{nm}={s}")
    if instr_i is not None:
        print(f"instructions={sums[instr_i]}")
    if cyc_i is not None:
        print(f"cycles={sums[cyc_i]}")
    if instr_i is not None and cyc_i is not None and sums[cyc_i] > 0:
        print(f"ipc={sums[instr_i] / sums[cyc_i]:.4f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
