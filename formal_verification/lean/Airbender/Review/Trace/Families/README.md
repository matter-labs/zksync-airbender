# Family execution claims

These modules state whole-trace execution for the original ADD/SUB plus
word-memory subset and the later standalone instruction families. Each family
specializes the step relation to its public decoder and registry, then states
agreement with native terminal PC/cells under explicit public boundaries and
accepted matching.

## Checked results

The family trace theorems take imported constraints, logical state/memory matching,
public initialization/program and their configuration/field conditions, then prove
actual Sail execution and terminal PC/cell agreement. Intermediate reads and row
order are derived, rather than supplied as the desired execution.

For [AddSub](AddSub/Theorems.lean), unchanged Sail retains the discarded-load
restriction; the Airbender profile and native-boot claims state their distinct
semantics and ROM view. [Subword memory](SubwordMemory/Theorems.lean) is RAM-only
here; [pooled execution](../Soundness.lean) separately includes public-ROM transport.
Jump termination retains its explicit canonical endpoint condition.

Each directory separates its step/trace definitions from its public trace theorem.

| Scope | Entry |
| --- | --- |
| Original ADD/SUB **and word-memory** subset | [AddSub/Theorems](AddSub/Theorems.lean) |
| Jump/branch/SLT | [JumpBranchSlt/Theorems](JumpBranchSlt/Theorems.lean) |
| MUL/DIV | [MulDiv/Theorems](MulDiv/Theorems.lean) |
| Shift/binop | [ShiftBinop/Theorems](ShiftBinop/Theorems.lean) |
| RAM subword memory | [SubwordMemory/Theorems](SubwordMemory/Theorems.lean) |

The AddSub entry retains the original two-family decoder; its name does not narrow
that scope. The other entries use their existing family-specific registries.

Read the execution relation, public inputs and acceptance/decoder membership
before following the proof. Check field minima, inverses, configuration and
terminal conditions on the exact theorem. These claims reach actual final PC/cells.
[Pooled composition](../Soundness.lean) admits all six families together.
[Local circuit claims](../../Circuits/README.md) have a different review scope.
