# shellcheck shell=bash
# THE WHOLE-MATRIX REPORTING LAYER, shared by every gate script in this directory.
#
# RR, 2026-08-13: "regarding any gates, as i said earlier, i do not want to reject anything based on a
# gate prematurely, i want to see the whole picture and then decide." So a gate run ALWAYS produces the
# complete board: every check is computed, every outcome is printed, a mismatch is RECORDED and the run
# carries straight on, and the last thing printed is the full cell matrix plus a NOT RUN block and a
# MISMATCHES block. One lane's mismatch never stops a later lane, and one cell's mismatch never masks
# the checks behind it on the same object.
#
# THE ONE CARVE-OUT: a check that cannot COMPUTE its answer has nothing to report. No binary, a run
# that printed nothing, an archive that will not extract, the wrong build flavour underneath, a digest
# that came back INVALID — those stop the CELL, are listed in the NOT RUN block with the reason, and
# never stop the run.
#
# Exit status is INFORMATION FOR AUTOMATION — non-zero when something mismatched — and nothing in any
# caller is conditional on it. The report prints either way.
#
# Contract for a caller:
#   lane_is <name>              tag every row that follows
#   bad <what> [want] [found]   RECORD a mismatch and carry on. Returns 0 on purpose, so it can never
#                               short-circuit a caller's `&&` chain or stand in for a decision.
#   notrun <what> <why>         a check that could not compute an answer
#   cellrow <group> <n> <ok>    one row of the matrix
#   gate_summary                the three blocks. Call it once, last, unconditionally.
#   $fail                       the mismatch count, and the exit status
#
# `lane_is` is spelled with a suffix because two cells in this suite already use `lane` as a local
# variable; bash keeps the namespaces apart, but a reader should not have to know that.

fail=0
LANE=main
GATE_UNIT=${GATE_UNIT:-cell}
MISMATCHES=()
LANE_ROWS=()
NOTRUN=()

note() { printf '%s\n' "$*"; }
lane_is() { LANE=$1; }

# The records are `|`-separated and a payload can itself be a markdown table row, so `|` is folded to
# `¦` on the way in. The inline print keeps the value verbatim, so nothing is lost.
bar() { printf '%s' "${1//|/¦}"; }

bad() { # bad <what was wrong> [expected] [found]
  fail=$((fail + 1))
  MISMATCHES+=("$LANE|$(bar "$1")|$(bar "${2-}")|$(bar "${3-}")")
  printf 'MISMATCH: %s\n' "$1"
  [ -n "${2-}" ] && printf '    expected: %s\n' "$2"
  [ -n "${3-}" ] && printf '    found:    %s\n' "$3"
  return 0
}

# Listed separately from a mismatch, because "we do not know" and "we know and it is wrong" are
# different readings and both are on the board.
notrun() { # notrun <what> <why>
  NOTRUN+=("$LANE|$(bar "$1")|$(bar "$2")")
  printf 'NOT RUN: %s — %s\n' "$1" "$2"
  return 0
}

cellrow() { # cellrow <group> <cells> <matched>
  LANE_ROWS+=("$LANE|$(bar "$1")|$2|$3|$(( $2 - $3 ))")
}

gate_summary() {
  local row l g c p m tc=0 tp=0 tm=0 what why i=0
  note ""
  note "================================================================================"
  note "THE WHOLE MATRIX — every ${GATE_UNIT} this run computed"
  note "================================================================================"
  note ""
  note "| lane | ${GATE_UNIT} group | ${GATE_UNIT}s | matched | mismatched |"
  note "| --- | --- | --- | --- | --- |"
  if [ ${#LANE_ROWS[@]} -gt 0 ]; then
    for row in "${LANE_ROWS[@]}"; do
      IFS='|' read -r l g c p m <<< "$row"
      note "| $l | $g | $c | $p | $m |"
      tc=$((tc + c)); tp=$((tp + p)); tm=$((tm + m))
    done
  fi
  note "| **total** | ${#LANE_ROWS[@]} ${GATE_UNIT} group(s) | **$tc** | **$tp** | **$tm** |"

  note ""
  if [ ${#NOTRUN[@]} -gt 0 ]; then
    note "### NOT RUN — ${#NOTRUN[@]} check(s) that could not compute an answer"
    note ""
    note "These are the carve-out: no binary, no output, an archive that would not extract, the wrong"
    note "build flavour underneath. They are not verdicts in either direction."
    note ""
    note "| lane | what | why |"
    note "| --- | --- | --- |"
    for row in "${NOTRUN[@]}"; do
      IFS='|' read -r l what why <<< "$row"
      note "| $l | $what | $why |"
    done
    note ""
  else
    note "### NOT RUN — none. Every check computed its answer."
    note ""
  fi

  if [ ${#MISMATCHES[@]} -gt 0 ]; then
    note "### MISMATCHES — ${#MISMATCHES[@]}"
    note ""
    note "Each row computed an answer and the answer was not the expected one. Nothing was rejected on"
    note "any one of them: the run continued to the end and the matrix above is complete."
    note ""
    note "| # | lane | what was wrong | expected | found |"
    note "| --- | --- | --- | --- | --- |"
    for row in "${MISMATCHES[@]}"; do
      i=$((i + 1))
      IFS='|' read -r l what why what2 <<< "$row"
      note "| $i | $l | $what | ${why:-—} | ${what2:-—} |"
    done
    note ""
    note "**$fail mismatch(es).** Read the whole board before deciding what any of them means."
  else
    note "### MISMATCHES — none."
    note ""
    note "**Every ${GATE_UNIT} computed its answer and every answer matched.** ALL GATES PASS."
  fi
  note ""
  note "exit status $fail — information for automation only; the report above is the deliverable and"
  note "is printed whatever the status."
}
