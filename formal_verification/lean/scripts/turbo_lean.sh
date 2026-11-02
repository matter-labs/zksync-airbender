#!/usr/bin/env bash
# Optional experiment. The official kernel validation gate remains required.
set -euo pipefail

project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"
tool_revision=2896cfd092758b8d0fc9977502dc036b0ab79921
tool_root="$project_dir/.lake/turbo-lean"
tool_source="$tool_root/source"
tool_binary="$tool_root/target/release/turbo-lean"
export ELAN_TOOLCHAIN
ELAN_TOOLCHAIN="$(cat lean-toolchain)"
[[ "$ELAN_TOOLCHAIN" == leanprover/lean4:v4.35.0 ]]
toolchain_root="$(elan run "$ELAN_TOOLCHAIN" lean --print-prefix)"
export PATH="$toolchain_root/bin:$PATH"
export TURBO_LEAN_BIN="$toolchain_root/bin/lean"
export TURBO_LEAN_HOME="$tool_root/cache"
export TURBO_LEAN_TELEMETRY=off
export CARGO_TARGET_DIR="$tool_root/target"
export CARGO_BUILD_JOBS=1 LEAN_NUM_THREADS=1
unset TURBO_LEAN_ALLOWED_AXIOMS TURBO_LEAN_ALLOWED_AXIOMS_FROM_CONFIG

if [[ "${1:-}" == install ]]; then
  mkdir -p "$tool_root"
  if [[ ! -d "$tool_source/.git" ]]; then
    git clone --filter=blob:none --no-checkout https://github.com/Th0rgal/turbo-lean.git "$tool_source"
    git -C "$tool_source" checkout --detach "$tool_revision"
  fi
  [[ "$(git -C "$tool_source" rev-parse HEAD)" == "$tool_revision" ]]
  git -C "$tool_source" diff --quiet HEAD --
  cd "$tool_source"
  cargo check --locked -p turbo-lean
  cargo build --locked --release -p turbo-lean
  exit
fi

if [[ ! -x "$tool_binary" ]]; then
  echo 'Run scripts/turbo_lean.sh install under the verification resource guard first.' >&2
  exit 2
fi
[[ "$(git -C "$tool_source" rev-parse HEAD)" == "$tool_revision" ]]
git -C "$tool_source" diff --quiet HEAD --

if [[ "${1:-}" == smoke ]]; then
  shift
  [[ "$#" == 0 ]]
  # The pinned tool rejects the real library's artifact needs. This trial has
  # one exact core-only source and does not replace the project configuration.
  python3 - "$project_dir" "$tool_binary" "$tool_root" "$tool_revision" <<'PY_TRIAL'
from pathlib import Path
import hashlib, json, re, subprocess, sys, tempfile, time
project, binary, tool_root = map(Path, sys.argv[1:4])
revision = sys.argv[4]
source = project / 'Airbender/Proofs/Tables/FiniteGridChecks.lean'
content = source.read_bytes()
if re.search(rb'^\s*(?:public\s+)?import\b', content, re.M):
    raise SystemExit('The smoke source must use only core Lean')
trial = Path(tempfile.mkdtemp(prefix='airbender-finite-grid-', dir='/tmp'))
copy = trial / 'FiniteGridChecks.lean'
copy.write_bytes(content)
for name in ('lean-toolchain', 'turbo-lean.toml'):
    (trial / name).write_bytes((project / name).read_bytes())
(trial / 'lakefile.toml').write_text('name = "airbender_finite_grid_trial"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "FiniteGridChecks"\n')
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
inputs = {str(path): digest(path) for path in
          (source, copy, trial / 'lean-toolchain', trial / 'turbo-lean.toml', trial / 'lakefile.toml', binary)}
assert inputs[str(source)] == inputs[str(copy)]
commands = [('stock', ['elan', 'run', 'leanprover/lean4:v4.35.0', 'lean', str(copy), '-o', str(trial / 'stock.olean')])]
for label in ('turbo-first', 'turbo-repeat'):
    commands.append((label, [str(binary), '--cache-dir', str(trial / 'cache'), '--no-auto-worktree-link',
        '--no-daemon', '--no-telemetry', '--max-memory-mb', '2560', '--json', 'check', str(copy),
        '--decl', 'Airbender.Verification.FiniteGridChecks.check_sound', '--project-dir', str(trial),
        '--jobs', '1', '--timeout', '900', '--kernel', 'standard']))
records = []
for label, command in commands:
    started = time.perf_counter()
    with (trial / (label + '.log')).open('w') as log:
        result = subprocess.run(command, cwd=trial, stdout=log, stderr=subprocess.STDOUT)
    records.append({'label': label, 'seconds': time.perf_counter() - started,
                    'exit': result.returncode, 'command': command})
    assert inputs == {path: digest(Path(path)) for path in inputs}, 'Smoke inputs changed'
    report = {'scope': 'One exact core-only checker; repeats are not proof edits',
              'tool_revision': revision, 'inputs': inputs, 'records': records}
    (trial / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    if result.returncode:
        raise SystemExit('Smoke failed; inspect ' + str(trial / (label + '.log')))
print(json.dumps({'passed': True, 'report': str(trial / 'results.json'),
                  'records': [{k: row[k] for k in ('label', 'seconds', 'exit')} for row in records]}))
PY_TRIAL
  exit
fi
exec "$tool_binary" --cache-dir "$TURBO_LEAN_HOME" --no-auto-worktree-link \
  --no-daemon --no-telemetry --max-memory-mb 2560 "$@"
