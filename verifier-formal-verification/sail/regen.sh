#!/usr/bin/env bash
# Regenerate the RV32 Sail RISC-V Lean model + vendored lean-sail into lean/sail-rv32/.
#
#   sail/regen.sh            # use `sail` + `z3` from PATH (or ~/.opam/sail/bin, ~/.local/bin)
#   sail/regen.sh --bootstrap-sail   # first build the pinned Sail compiler with opam (needs opam >= 2, gmp, git)
#
# Everything is pinned below (and mirrored in sail/PINS.md). Nothing is taken from "latest".
# Environment overrides: WORK (scratch dir, default <repo>/build/sail-work), OUT (default <repo>/lean/sail-rv32),
#   VARIANT=proof|default|executable (see sail/README.md), KEEP_WORK=1, CONFIG=<path to a Sail config json>.
set -euo pipefail

# ---------------------------------------------------------------- pins
SAIL_REPO=https://github.com/rems-project/sail.git
SAIL_REV=2ba321281cea18485f783da05c8a147a45d6b980      # "Sail 0.20.3 (sail2 @ 2ba3212)", 2026-10-09
SAIL_VERSION=0.20.3
SAILRISCV_REPO=https://github.com/riscv/sail-riscv.git
SAILRISCV_REV=6136f84326f41dbaf72daf43a3787195ea3bd1c6  # tag 2026-10-12-6136f84 (master, 2026-10-09)
LEANSAIL_REPO=https://github.com/rems-project/lean-sail.git
LEANSAIL_REV=c816ea7ad03cce98d51acee252540fd4215fede8   # tag v6 (2026-09-18), upstream toolchain v4.29.0
LEAN_TOOLCHAIN=leanprover/lean4:v4.34.1
OPAM_SWITCH=sail
OCAML_VERSION=5.4.1

# Sail module scope: the project root modules whose transitive `requires` are generated.
# See sail/README.md for why each is listed.
# SCOPE=full (default) generates every module (`--all-modules`, what upstream's CMake does); SCOPE=min is the short
# list below. NOTE: with SCOPE=min `currentlyEnabled`/`execute` are partial functions (scattered clauses of the omitted
# extensions are missing), so e.g. `init_model` fails with "Pattern match failure ... Zicboz"; see sail/README.md.
case "${SCOPE:-full}" in
  full) MODULES=(--all-modules) ;;
  min)  MODULES=(main I_insts M_insts Zicsr_insts) ;;
  *) echo "SCOPE must be full|min" >&2; exit 2 ;;
esac

LEAN_PKG=SailRV32          # Lean package/library/namespace name for the generated model

# ---------------------------------------------------------------- paths
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
WORK="${WORK:-$ROOT/build/sail-work}"
OUT="${OUT:-$ROOT/lean/sail-rv32}"
VARIANT="${VARIANT:-proof}"
# Machine config, baked into the generated Lean at Sail->Lean time (`sail --config`); see sail/README.md.
# config/rv32.json is the unmodified upstream config (kept for reference / `diff`); the default is ours.
CONFIG="${CONFIG:-$HERE/config/airbender-base.json}"
CONFIG_NAME="$(basename "$CONFIG")"
PATCHES="$HERE/patches"

BOOTSTRAP=0
for a in "$@"; do case "$a" in
  --bootstrap-sail) BOOTSTRAP=1 ;;
  -h|--help) sed -n 2,9p "${BASH_SOURCE[0]}"; exit 0 ;;
  *) echo "unknown argument: $a" >&2; exit 2 ;;
esac; done

log() { echo ">> $*" >&2; }
fetch_rev() { # repo rev dir : shallow checkout of exactly <rev>
  local repo=$1 rev=$2 dir=$3
  rm -rf "$dir"; mkdir -p "$dir"
  git -C "$dir" init -q
  git -C "$dir" remote add origin "$repo"
  git -C "$dir" fetch -q --depth 1 origin "$rev"
  git -C "$dir" checkout -q FETCH_HEAD
  [[ "$(git -C "$dir" rev-parse HEAD)" == "$rev" ]] || { echo "rev mismatch in $dir" >&2; exit 1; }
}

mkdir -p "$WORK"

# ---------------------------------------------------------------- 0. Sail compiler
export PATH="$HOME/.opam/$OPAM_SWITCH/bin:$HOME/.local/bin:$PATH"
if (( BOOTSTRAP )); then
  command -v opam >/dev/null || { echo "opam not found (see sail/README.md)" >&2; exit 2; }
  log "bootstrap Sail $SAIL_REV into opam switch '$OPAM_SWITCH' (ocaml $OCAML_VERSION)"
  [[ -d "$HOME/.opam" ]] || opam init --bare --disable-sandboxing -y
  opam switch list --short | grep -qx "$OPAM_SWITCH" || opam switch create "$OPAM_SWITCH" "$OCAML_VERSION" -y
  fetch_rev "$SAIL_REPO" "$SAIL_REV" "$WORK/sail"
  ( cd "$WORK/sail"
    eval "$(opam env --switch="$OPAM_SWITCH")"
    opam install . --deps-only -y
    make install )
fi
command -v sail >/dev/null || { echo "sail not found; run with --bootstrap-sail" >&2; exit 2; }
command -v z3   >/dev/null || { echo "z3 not found on PATH (Sail needs z3 >= 4.8 for --memo-z3)" >&2; exit 2; }
sail_v="$(sail --version)"
case "$sail_v" in
  "Sail $SAIL_VERSION (sail2 @ $SAIL_REV)") ;;
  *) echo "wrong Sail: '$sail_v' (want 'Sail $SAIL_VERSION (sail2 @ $SAIL_REV)')" >&2; exit 2 ;;
esac

# ---------------------------------------------------------------- 1. sail-riscv (+ patch)
log "fetch sail-riscv $SAILRISCV_REV"
fetch_rev "$SAILRISCV_REPO" "$SAILRISCV_REV" "$WORK/sail-riscv"
for p in "$PATCHES"/sail-riscv-*.patch; do
  log "apply $(basename "$p")"; git -C "$WORK/sail-riscv" apply --whitespace=nowarn "$p"
done
req="$(tr -d '[:space:]' < "$WORK/sail-riscv/cmake/sail_required_version.txt")"
[[ "$req" == "$SAIL_VERSION" ]] || { echo "sail-riscv requires Sail $req, pinned $SAIL_VERSION" >&2; exit 1; }

# ---------------------------------------------------------------- 2. lean-sail (+ patch), vendored
log "fetch lean-sail $LEANSAIL_REV"
fetch_rev "$LEANSAIL_REPO" "$LEANSAIL_REV" "$WORK/lean-sail"
for p in "$PATCHES"/lean-sail-*.patch; do
  log "apply $(basename "$p")"; git -C "$WORK/lean-sail" apply --whitespace=nowarn "$p"
done

# ---------------------------------------------------------------- 3. Sail -> Lean
# VARIANT (see sail/README.md):
#   proof      (default) upstream's default flags (`--lean-noncomputable`: nothing is compiled, encdec_* noncomputable) but
#              with RiscvExtrasExecutable.lean, i.e. the platform/softfloat hooks are concrete (panicking) definitions
#              instead of axioms. Works with SCOPE=full. Kernel-evaluable, no custom axioms.
#   default    upstream's default: as `proof`, but the hooks are `axiom`s (RiscvExtras.lean).
#   executable upstream's "executable" flags: no `noncomputable`, so code is generated (`#eval` works). Fails with
#              SCOPE=full (Lean IR cannot represent `instruction`, which has > 256 constructors); needs SCOPE=min.
NC_FLAGS=(--lean-noncomputable
  --lean-noncomputable-function encdec_forwards          --lean-noncomputable-function encdec_backwards
  --lean-noncomputable-function encdec_forwards_matches  --lean-noncomputable-function encdec_backwards_matches
  --lean-noncomputable-function encdec_compressed_forwards         --lean-noncomputable-function encdec_compressed_backwards
  --lean-noncomputable-function encdec_compressed_forwards_matches --lean-noncomputable-function encdec_compressed_backwards_matches)
case "$VARIANT" in
  proof)      EXTRAS=RiscvExtrasExecutable.lean; FLAGS=("${NC_FLAGS[@]}") ;;
  default)    EXTRAS=RiscvExtras.lean;           FLAGS=("${NC_FLAGS[@]}") ;;
  executable) EXTRAS=RiscvExtrasExecutable.lean; FLAGS=() ;;
  *) echo "VARIANT must be proof|default|executable" >&2; exit 2 ;;
esac

GEN="$WORK/generated"; rm -rf "$GEN"; mkdir -p "$GEN"
log "sail --lean ($VARIANT) modules: ${MODULES[*]}"
( cd "$WORK/sail-riscv/model"
  sail --strict-var --strict-bitvector --strict-exponentials --require-version "$SAIL_VERSION" \
    --memo-z3 --memo-z3-path "$WORK/z3-cache.memo" \
    --config "$CONFIG" \
    --lean --lean-output-dir "$GEN" --lean-force-output \
    --lean-non-beq-type instruction --lean-non-beq-type instr_info --lean-non-beq-type HartState \
    --lean-non-beq-type ExecutionResult --lean-non-beq-type Step \
    "${FLAGS[@]}" \
    --lean-import-file "../handwritten_support/$EXTRAS" \
    -o "$LEAN_PKG" \
    riscv.sail_project "${MODULES[@]}" ) 2> "$WORK/sail.log"
[[ -f "$GEN/$LEAN_PKG/$LEAN_PKG.lean" ]] || { tail -30 "$WORK/sail.log"; echo "Sail did not generate $LEAN_PKG" >&2; exit 1; }

# Lean 4.34 compat (only post-processing of generated code): Sail emits `assert c "msg"` as a do-element calling
# lean-sail's `Sail.assert`; since Lean 4.3x the bare identifier `assert` no longer elaborates as that function
# ("Function expected at false"). Quoting the identifier selects the lean-sail definition again. Pure rename.
n_before="$(grep -rhoP '(^|[\s(])assert(?= )' "$GEN/$LEAN_PKG" | wc -l)"
find "$GEN/$LEAN_PKG" -name '*.lean' -print0 | xargs -0 perl -pi -e 's/(^|[\s(])assert(?= )/$1«assert»/'
log "quoted $n_before uses of \`assert\`"

# Build-time workaround: with Lean 4.34's new `do` elaborator, `print_rvfi_exec` (RVFI-DII trace printing; not used by
# the ISA semantics) takes >17 min and ~13 GB to elaborate (exponential in a run of ~20 unit-valued `(pure (f (<- x)))`
# statements); with the legacy elaborator it takes ~1 s. Select the legacy elaborator for that one file only.
perl -pi -e 's/^(set_option maxRecDepth .*)$/$1\nset_option backward.do.legacy true/' "$GEN/$LEAN_PKG/$LEAN_PKG/RvfiDii.lean"
grep -q 'backward.do.legacy' "$GEN/$LEAN_PKG/$LEAN_PKG/RvfiDii.lean" || { echo "RvfiDii patch failed" >&2; exit 1; }

# ---------------------------------------------------------------- 4. assemble the Lake package
log "assemble $OUT"
rm -rf "$OUT"; mkdir -p "$OUT"
cp -r "$GEN/$LEAN_PKG/$LEAN_PKG" "$GEN/$LEAN_PKG/$LEAN_PKG.lean" "$OUT/"
rm -rf "$WORK/lean-sail/.git"
cp -r "$WORK/lean-sail" "$OUT/lean-sail"
cp "$HERE/smoke/SailRV32Smoke.lean" "$OUT/SailRV32Smoke.lean"
cp "$CONFIG" "$OUT/$CONFIG_NAME"            # the compile-time config the model was generated with
printf '%s\n' "${LEAN_TOOLCHAIN}" > "$OUT/lean-toolchain"
cat > "$OUT/lakefile.toml" <<EOF
# GENERATED by sail/regen.sh -- do not edit by hand.
name = "sail_rv32"
defaultTargets = ["$LEAN_PKG"]
moreLeanArgs = ["--tstack=400000"]

[[lean_lib]]
name = "$LEAN_PKG"
leanOptions.weak.linter.style.nameCheck = false
moreLeancArgs = ["-fbracket-depth=500"]

# `lake build SailRV32Smoke`: kernel-checked smoke test (sail/smoke/SailRV32Smoke.lean); not a default target
[[lean_lib]]
name = "SailRV32Smoke"
leanOptions.weak.linter.style.nameCheck = false

# lean-sail v6 @ ${LEANSAIL_REV:0:7}, vendored with sail/patches/lean-sail-*.patch applied (Lean 4.34 compat)
[[require]]
name = "Sail"
path = "lean-sail"
EOF
cat > "$OUT/PROVENANCE.txt" <<EOF
GENERATED by sail/regen.sh (variant: $VARIANT)
sail            $SAIL_VERSION @ $SAIL_REV
sail-riscv      $SAILRISCV_REV (+ sail/patches/sail-riscv-*.patch)
lean-sail       $LEANSAIL_REV (+ sail/patches/lean-sail-*.patch), vendored in lean-sail/
lean toolchain  $LEAN_TOOLCHAIN
sail modules    ${MODULES[*]}
config          $CONFIG_NAME
EOF
log "done: $(find "$OUT" -name '*.lean' -not -path '*/lean-sail/*' | wc -l) generated .lean files, $(du -sh "$OUT" | cut -f1) total"
(( ${KEEP_WORK:-0} )) || { rm -rf "$WORK/sail-riscv" "$WORK/lean-sail" "$GEN" "$WORK/z3-cache.memo" "$WORK/sail.log"; rmdir "$WORK" 2>/dev/null || true; }
echo "next: (cd $OUT && lake build)" >&2
