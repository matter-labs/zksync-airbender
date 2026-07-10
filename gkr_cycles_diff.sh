#!/usr/bin/env bash
set -euo pipefail

# Diff verifier flamegraph cycle counts against a git baseline. Reads the
# `total_samples` attribute from each `verifier/gkr_flamegraph_<circuit>.svg`
# in the working tree and compares to the same path at the chosen revision.
#
# The script does not regenerate flamegraphs; run `./gkr_test.sh <mode> transpiler`
# first if you want fresh numbers.

die() { echo "ERROR: $*" >&2; exit 2; }

BASELINE="HEAD"
CIRCUITS=()

usage() {
  cat <<EOF
Usage: $0 [--baseline REV] [circuit ...]

Options:
  --baseline REV   Git revision to compare against. Defaults to HEAD; pass
                   origin/av_gkr_compiler for branch-level comparison.
  -h, --help       Show this message.

Args:
  circuit ...      Full circuit names (e.g. add_sub_lui_auipc_mop_sec_80).
                   Defaults to every flamegraph found in verifier/.

Examples:
  $0
  $0 --baseline origin/av_gkr_compiler
  $0 unified_reduced_machine_sec_80
  $0 --baseline HEAD~5 jump_branch_slt_sec_80 mem_word_only_sec_80
EOF
  exit 1
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage ;;
    --baseline) BASELINE="$2"; shift 2 ;;
    --) shift; CIRCUITS+=("$@"); break ;;
    -*) die "unknown option: $1" ;;
    *) CIRCUITS+=("$1"); shift ;;
  esac
done

[[ -d verifier ]] || die "must run from airbender repo root (verifier/ not found)"

# Default to every flamegraph in the working tree, sorted.
if [[ ${#CIRCUITS[@]} -eq 0 ]]; then
  while IFS= read -r f; do
    CIRCUITS+=("$(basename "$f" .svg | sed 's|^gkr_flamegraph_||')")
  done < <(ls verifier/gkr_flamegraph_*.svg 2>/dev/null | sort)
fi

[[ ${#CIRCUITS[@]} -gt 0 ]] || die "no flamegraphs found in verifier/"

git rev-parse --verify --quiet "$BASELINE" >/dev/null \
  || die "baseline revision not found: $BASELINE"

# Extract total_samples from an SVG read from stdin. Empty stdin → "MISSING".
read_samples() {
  local content
  content=$(cat)
  if [[ -z "$content" ]]; then
    echo "MISSING"
  else
    echo "$content" | grep -o 'total_samples="[0-9]*"' | head -1 | grep -o '[0-9]*' || echo "MISSING"
  fi
}

# Header
printf "### Cycle counts (baseline: %s)\n\n" "$BASELINE"
printf "| %-40s | %12s | %12s | %12s |\n" "Circuit" "Baseline" "Current" "Delta"
printf "| %s | %s | %s | %s |\n" \
  "----------------------------------------" \
  "-----------:" "-----------:" "-----------:"

total_b=0
total_c=0
have_total=true

for circuit in "${CIRCUITS[@]}"; do
  path="verifier/gkr_flamegraph_${circuit}.svg"

  current="MISSING"
  [[ -f "$path" ]] && current=$(read_samples <"$path")

  # `git show` outside the pipeline so we can detect "file missing at baseline"
  # without tripping pipefail (which would let `read_samples` produce one
  # MISSING and then `|| echo MISSING` produce a second, breaking the equality
  # check below).
  baseline="MISSING"
  if baseline_blob=$(git show "${BASELINE}:${path}" 2>/dev/null); then
    baseline=$(printf '%s' "$baseline_blob" | read_samples)
  fi

  if [[ "$baseline" = "MISSING" || "$current" = "MISSING" ]]; then
    printf "| %-40s | %12s | %12s | %12s |\n" "$circuit" "$baseline" "$current" "n/a"
    have_total=false
    continue
  fi

  delta=$((current - baseline))
  sign=""
  [[ $delta -gt 0 ]] && sign="+"
  # Percentage with 2 decimals via integer math (no bc/awk dependency).
  if [[ $baseline -ne 0 ]]; then
    pct_hundredths=$((delta * 10000 / baseline))
    abs=$(( pct_hundredths < 0 ? -pct_hundredths : pct_hundredths ))
    int=$((abs / 100))
    frac=$((abs % 100))
    pct_sign=""
    if   [[ $pct_hundredths -gt 0 ]]; then pct_sign="+"
    elif [[ $pct_hundredths -lt 0 ]]; then pct_sign="-"
    fi
    pct=$(printf "%s%d.%02d%%" "$pct_sign" "$int" "$frac")
    delta_str=$(printf "%s%d (%s)" "$sign" "$delta" "$pct")
  else
    delta_str=$(printf "%s%d" "$sign" "$delta")
  fi
  printf "| %-40s | %12d | %12d | %12s |\n" "$circuit" "$baseline" "$current" "$delta_str"
  total_b=$((total_b + baseline))
  total_c=$((total_c + current))
done

if $have_total; then
  total_d=$((total_c - total_b))
  sign=""
  [[ $total_d -gt 0 ]] && sign="+"
  if [[ $total_b -ne 0 ]]; then
    pct_hundredths=$((total_d * 10000 / total_b))
    abs=$(( pct_hundredths < 0 ? -pct_hundredths : pct_hundredths ))
    int=$((abs / 100))
    frac=$((abs % 100))
    pct_sign=""
    if   [[ $pct_hundredths -gt 0 ]]; then pct_sign="+"
    elif [[ $pct_hundredths -lt 0 ]]; then pct_sign="-"
    fi
    pct=$(printf "%s%d.%02d%%" "$pct_sign" "$int" "$frac")
    total_str=$(printf "%s%d (%s)" "$sign" "$total_d" "$pct")
  else
    total_str=$(printf "%s%d" "$sign" "$total_d")
  fi
  printf "| %-40s | %12d | %12d | %12s |\n" "**TOTAL**" "$total_b" "$total_c" "$total_str"
fi
