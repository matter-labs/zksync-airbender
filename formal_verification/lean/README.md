# Circuit verification

## What is checked

[Verification status](VERIFICATION_STATUS.md) lists every circuit, checked coverage
and open tasks. It is updated after each completed task.

The proof path is:

```text
no-cache JSON → native Clean constraints → Sail execution (or pinned custom spec)
```

Claims are conditional on explicit interfaces. The imported richer constraints are
the current target; compiled-gate and cryptographic argument soundness are deferred.

## Read these first

The source tree follows the review boundary:

```text
Airbender/
  Review/
    Circuits/<family>/  row contracts, references, mappings and local claims
      Tables/          modeled circuit setup and controller encodings
    Helpers/           imported rows/ports, matching, initialization and pre-states
      Tables/          shared range, byte and subword tables
    Trace/             instruction execution, terminal realization and spans
  Proofs/    supporting proofs checked by Lean
  Import/    JSON parser, coefficient decoding and emission; audit separately
  Checks/    axiom audit
```

Choose the reading path for the claim being reviewed:

1. **Individual circuit soundness:** start with the circuit's claim and model,
   such as [ADD/SUB claims](Airbender/Review/Circuits/AddSub/Theorems.lean) and
   [its model](Airbender/Review/Circuits/AddSub/Model.lean). Follow the named artifact
   and reference in that directory, then the shared [history inputs](Airbender/Review/Helpers/Interfaces.lean),
   [public initialization](Airbender/Review/Helpers/Boundary.lean),
   [accepted rows/matching](Airbender/Review/Helpers/Model.lean),
   [decoder membership](Airbender/Review/Helpers/PooledProgram.lean) and
   [selected pre-state](Airbender/Review/Helpers/RowContext.lean).
   Initialized history remains necessary to derive reads and bounds.
2. **Whole-trace execution:** start with [composed claims](Airbender/Review/Trace/Soundness.lean),
   [execution and terminal realization](Airbender/Review/Trace/Execution.lean), and
   [public pooled boundaries](Airbender/Review/Helpers/PooledBoundary.lean).
   [ADD/SUB trace claims](Airbender/Review/Trace/Families/AddSub/Theorems.lean)
   retain the original combined ADD/SUB and word-memory scope. Other standalone
   family execution also lives in `Trace/Families/`; worker port transport
   and complete hash protocols live in `Trace/Workers/` and `Trace/Delegation/`.
   [Unified composition](Airbender/Review/Trace/UnifiedReduced/Theorems.lean)
   retains its existing caller/profile limitations.

Circuit definitions and shared helpers do not import whole-execution contracts.
The Jump/branch/SLT, MUL/DIV and shift/binop theorem modules retain a transitive
proof dependency through `Proofs/Trace/PooledExecution.lean`. That implementation
reuses jump retirement/composition lemmas; reviewing their local statements and
assumptions does not require reviewing a whole-run claim. Proof files keep their
existing organization. The review check guards these three documented exceptions.

The shared `Realizes` property
says that Sail execution reaches the terminal PC and register/RAM values; native
boot fixes the readonly ROM interpretation explicitly. Its implementation lives in
`Proofs/`; reading the calculation lemmas is optional. The primary
`pooled_native_soundness` claim composes arithmetic/word memory, jump/comparison,
unsigned mul/div, shifts/binops and RAM/ROM subword instructions through one
initialized history. Per-row bounds and reads are proved internally. ROM loads
use public bytes; the prover's ROM permutation slots remain zero.
`NonDeterminism.Pooled.native_soundness` uses the same public boundary for mixed
execution with independent external reads/hints and proves the consumed count.

| Question | Entry point |
| --- | --- |
| What does ADD/SUB assume? | [Per-circuit model](Airbender/Review/Circuits/AddSub/Model.lean): `circuitModel` and `InterfaceAssumptions`; [claim](Airbender/Review/Circuits/AddSub/Theorems.lean): `babyBear_soundness`. |
| What is proved for a whole trace? | [Primary standard and mixed claims](Airbender/Review/Trace/Soundness.lean): `pooled_native_soundness` and `NonDeterminism.Pooled.native_soundness`. [Supporting claims](Airbender/Proofs/Trace/Claims.lean) preserve physical-image and restricted-subset coverage. |
| What inputs and assumptions does it use? | [Pooled public inputs](Airbender/Review/Helpers/PooledBoundary.lean): `PooledBootInputs`; [shared trace relations](Airbender/Review/Helpers/Model.lean): `Accepted`; [decoder membership](Airbender/Review/Helpers/PooledProgram.lean): `PooledDecoded`. |
| How do external reads compose? | [Independent stream boundary and custom clause](Airbender/Review/Helpers/ExternalInput.lean); [pooled mixed execution](Airbender/Review/Trace/PooledNonDeterminism.lean) defines the whole-run conclusion. The primary mixed claim proves final PC/cells and exact consumption across all six families plus reads/hints. |
| What do the shared definitions mean? | [Soundness](Airbender/Review/Helpers/Properties.lean), [word encoding](Airbender/Review/Helpers/Word.lean), [fields](Airbender/Review/Helpers/Field.lean), [Sail interface](Airbender/Review/Helpers/Sail.lean), and [shared trace history](Airbender/Review/Helpers/SailHistory.lean). |
| How are delegation effects connected? | [Pooled caller claims](Airbender/Review/Trace/Delegation/CallerTheorems.lean) and [unified caller claims](Airbender/Review/Trace/UnifiedReduced/Theorems.lean) derive reads, bounds, x0 and actual worker effects from one initialized history. `shared_span_soundness` connects complete caller-only hash references to that same shared terminal state. `Caller.caller_cycles_soundness` binds actual fetch, worker observations and PC retirement at the same cycle boundaries under its physical/code profile. Complete selected hash windows are checked; full custom-CSR ABI, broader span composition, whole execution with callers and zero-clock exclusion remain open. |
| How are unified standard/custom rows connected? | [Combined registry and public inputs](Airbender/Review/Helpers/UnifiedReduced/Program.lean), with `Mixed.execution_soundness` in [unified claims](Airbender/Review/Trace/UnifiedReduced/Theorems.lean): original public decoding, shared native boot/ROM history, exact instruction retirement and final PC/cells. Delegation callers remain outside this registry. |
| What is covered elsewhere or still open? | [Circuit and task tables](VERIFICATION_STATUS.md), with links to each family's claims. |
| Which restrictions have concrete witnesses? | [Checked scope boundaries](TRUST_AND_REVIEW.md#checked-scope-boundaries): inactive rows, terminal PC, discarded loads and the three delegation ABI gaps. |
| What requires separate trust review? | [Trust boundaries](TRUST_AND_REVIEW.md): importer, Sail generation, modeled tables and logical argument enforcement. |

Trace proofs derive operand bounds from public initialization, preserved writes
and latest-write/read consistency. They also derive the row decoder and register
interfaces. These are not caller-supplied per-row assumptions. Public initial
state/program, field and platform conditions, and logical matching remain explicit.
The status tables identify additional unresolved conditions, including jump
terminal-PC normalization, that any pooled claim must retain until discharged.

The [ADD/SUB](Airbender/Review/Circuits/AddSub/Model.lean),
[jump/branch/comparison](Airbender/Review/Circuits/JumpBranchSlt/Model.lean),
[word-memory](Airbender/Review/Circuits/WordMemory/Model.lean),
[mul/div](Airbender/Review/Circuits/MulDiv/Model.lean),
[shift/binop](Airbender/Review/Circuits/ShiftBinop/Model.lean) and
[subword-memory](Airbender/Review/Circuits/SubwordMemory/Model.lean) models keep their per-circuit
assumption lists: public initialization, modeled tables and configuration. ADD/SUB requires an
initialized register domain; word/subword memory lists the ordinary-address domain and
flat-memory platform configuration. Shift/binop requires only public initialization.
Jump/comparison keeps aligned code and terminal-PC normalization; branches/jumps
need public `misa`, and only JALR needs Machine/MLPE-clear configuration.
Trace helpers derive operand/immediate/PC bounds, actual reads and preprocessing.
Their state mappings apply earlier native writes without assuming read values.
Standalone calculation interfaces remain internal in each family's `Proofs/RowModel.lean`.
Named columns are checked against artifact metadata; faithful JSON import itself
is trusted. Upstream sources remain in `vendor/`, `generated/` and `.lake/packages`.

## Clean and Sail

Clean is pinned at `1e563b9c27991b3795eb440c1ee0757edb4ce8b1`.
[Preparation](scripts/prepare_clean.py) checks original source hashes before applying
Lean `v4.31.0` compatibility fixes: a tactic import, factory registration metadata,
and explicit proof reductions. Constraint semantics, algorithms and theorem
statements are unchanged; repaired proof terms are kernel-checked and axiom-audited.
The original Keccak permutation reference compiles unchanged; the [Theta column](Airbender/Review/Circuits/Keccak/Theta.lean) and [two-call Chi row](Airbender/Review/Circuits/Keccak/Chi.lean) claims use its `thetaXor` and `chi` directly. We use Clean's native
`Expression`, `FlatOperation.assert`, `StaticTable`, `FlatOperation.lookup`,
`Environment` and `ConstraintsHoldFlat`.
The witness-generation DSL and full `FormalCircuit` bundle are not used.
Airbender's two-16-bit-limb representation is preserved.

The reference uses [unmodified upstream Sail clauses](vendor/sail-riscv/source/model/extensions/I/base_insts.sail)
and [their generated Lean definitions](generated/sail-rv32/SailRV32.lean).
The original ADD/SUB clause is `execute(RTYPE(...))`; ADDI is `execute(ITYPE(...))`;
LUI/AUIPC use `execute(UTYPE(...))`. The Lean interface calls the generated
`execute_RTYPE`, `execute_ITYPE` and `execute_UTYPE` directly.
Unsigned division uses the original `execute_DIV`/`execute_REM` clauses from
[the M-extension source](vendor/sail-riscv/source/model/extensions/M/mext_insts.sail).
[Provenance and regeneration](generated/sail-rv32/README.md) record model/compiler/runtime
pins. The normal four-byte nextPC assignment is extracted verbatim from upstream
`run_hart_active` and compiled by Sail, then composed with execution and `tick_pc`.
Extraction and path selection remain unchecked connections; full fetch/exception
handling and memory arguments are outside the claim. Standard instructions have no local replacement spec;
custom arithmetic uses the [pinned project definitions](vendor/airbender/00-master.md#supported-instruction-set-and-custom-operations).
Representation and execution lemmas live in `Proofs/Arithmetic/Word.lean` and
`Proofs/Sail/RiscV.lean`.

## Reproduce

Run from `formal_verification/lean`:

```sh
python3 scripts/prepare_clean.py
python3 - <<'PYTESTS'
from pathlib import Path
import subprocess
modules = [".".join(path.with_suffix("").parts)
           for path in sorted(Path("Tests").rglob("*.lean"))]
subprocess.run(["lake", "build", "Airbender", "airbender_import",
                "airbender_tests", "Airbender.Checks.Axioms", *modules], check=True)
PYTESTS
lake env lean Airbender/Checks/Axioms.lean
lake exe airbender_tests
python3 scripts/check_review.py
```

The audit lists theorem axiom dependencies. The checked claims use only standard
Lean axioms; no `sorry` or project axioms are admitted. Importer tests are not
proofs of faithful parsing. Subsequent work is in [the plan](FORMAL_VERIFICATION_PLAN.md).
The [review check](scripts/check_review.py) uses Lean's compiled declaration locations to require an explicit
axiom root for every source-declared public theorem in `Review/`. It also resolves
guide declaration names and local file/heading links. Source-only Rust/Sail names
are listed separately in the script; their fidelity remains a trust boundary.
It also checks context/trace import separation and the documented proof-assembly dependencies.

For the integrated trace proof and regressions:

```sh
lake build Tests.TraceImport Airbender.Checks.TraceAxioms
lake env lean Airbender/Checks/TraceAxioms.lean
```

This focused target checks ADD/SUB, word-memory and jump/branch/SLT native
clock/port artifacts, rollover/rejection
fixtures and timestamp/address/value importer guards. The primary public surface is
[Trace/Soundness.lean](Airbender/Review/Trace/Soundness.lean), with the native
matching and initial-clock conditions in [Trace/Model.lean](Airbender/Review/Helpers/Model.lean).
The history fixtures check rejection of an unmatched previous-write timestamp
and complete per-address paths with interleaved accesses and changing values.
A changed operand/result pair satisfies the local ADD constraints but is rejected
by native matching because the fabricated read has no matching previous write.
The nonzero-register fixture checks the explicit initialization writes required
by Clean's zero-initial online-memory semantics.
The [initial-image constructor](Airbender/Review/Helpers/InitialImage.lean) reads
public Sail state directly. Its fixtures check nonzero GPRs, x0, little-endian
RAM and rejection of missing cells; extraction proves initial bounds and uniqueness.

With the Lean 4 VS Code extension, open this project folder and inspect a scratch
file in the Infoview:

```lean
import Airbender.Review.Circuits.AddSub.Artifact
#print Airbender.AddSub.importedConstraints
```
