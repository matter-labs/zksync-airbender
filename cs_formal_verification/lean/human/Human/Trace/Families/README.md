# Family execution claims

These modules state whole-trace execution for the original ADD/SUB plus
word-memory subset and the later standalone instruction families. Each family
specializes the step relation to its public decoder and registry, then states
agreement with native terminal PC/cells under explicit public boundaries and
accepted matching.

## Checked results

Each trace claim states its inputs, acceptance, decoder membership and run conclusion.
Each family trace claim has a separate `…SatisfiableClaim`, witnessed by a one-row
trace fetched from ROM ([Satisfiable/Families](../../../../proven/Proven/Final/Trace/Satisfiable/Families.lean)).

The family trace theorems take imported constraints, logical state/memory matching,
public initialization/program and their field conditions, then prove
that the rows are a run of `RV.run` and agree with the terminal PC/cells. Intermediate reads and row
order are derived, rather than supplied as the desired execution.

For [AddSub](AddSub/RVTheorems.lean), a load into x0 only advances
the PC in the spec, so no load restriction applies; the native-boot claim seeds RAM from the inits/teardowns
Init tokens. [Subword memory](SubwordMemory/RVTheorems.lean) is RAM-only
here; [pooled execution](../RVSoundness.lean) separately includes public-ROM transport.
Jump termination retains its explicit canonical terminal-PC condition (`terminalCanonical`).

Each directory separates its step/trace definitions from its public trace theorem.

| Scope | Entry |
| --- | --- |
| Original ADD/SUB **and word-memory** subset | [AddSub/RVTheorems](AddSub/RVTheorems.lean) |
| Jump/branch/SLT | [JumpBranchSlt/RVTheorems](JumpBranchSlt/RVTheorems.lean) |
| MUL/DIV | [MulDiv/RVTheorems](MulDiv/RVTheorems.lean) |
| Shift/binop | [ShiftBinop/RVTheorems](ShiftBinop/RVTheorems.lean) |
| RAM subword memory | [SubwordMemory/RVTheorems](SubwordMemory/RVTheorems.lean) |

The AddSub entry retains the original two-family decoder; its name does not narrow
that scope. The other entries use their existing family-specific registries.

Read the execution relation, public inputs and acceptance/decoder membership
before following the proof. Check field minima, inverses and
terminal conditions on the exact theorem. These claims reach the final PC/cells of an `RV.run`.
[Pooled composition](../RVSoundness.lean) admits all six families together.
[Local circuit claims](../../Circuits/README.md) have a different review scope.
