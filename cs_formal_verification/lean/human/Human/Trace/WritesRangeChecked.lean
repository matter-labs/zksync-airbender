module
public import Human.Helpers.Core.BabyBearPrime
public import Human.Helpers.Context.RVPooledBoundary
public import Human.Helpers.Decoder.RVExternalInput
public import Human.Helpers.UnifiedReduced.Registry
public import Human.Helpers.Delegation.Operations
public import Human.Circuits.KeccakSplit.Native
public import Human.Circuits.InitsTeardowns.Model

@[expose] public section

/-! Every write of a formalised circuit is range-checked: the write side of the inventory behind the open item
    `InitsTeardowns.MemoryArgumentReadsBounded`.

    The write sites covered, per circuit set: every port of every row of the six pooled CPU families (ADD/SUB with the
    CSR 0x7C0 forms, word memory, subword memory, shift/binop, mul/div, jump/branch/SLT), of the unified reduced
    machine, of the four delegation workers (bigint, Blake2s G, Blake2s round, Keccak) and of the three split Keccak
    workers (column parity, theta+rho, chi), and every `Init` tuple of the inits/teardowns sets (standalone and
    inline). A row's write is bounded whenever the row's reads are: a value the row computes is range-checked by its
    constraints, a value it only moves (a readonly port's refresh, a stored or copied register) is one of its reads.
    The statements mention no machine state. Proven in slop/Slop/Final/Trace/WritesRangeChecked.lean. -/

namespace Airbender.Trace

/-- The writes of one row's memory steps (one read token and one write token per port) are range-checked: every
    written word is bounded (two 16-bit limbs) whenever every word the row read is. -/
def WritesRangeChecked {p : Nat} (steps : List (MemoryToken p × MemoryToken p)) : Prop :=
  (∀ step ∈ steps, step.1.word.Bounded) → ∀ step ∈ steps, step.2.word.Bounded

/-- The six pooled families, with the standard or the CSR 0x7C0-extended RV program table: every row of an accepted,
    decoded trace has range-checked writes. The boot inputs supply the modeled word-ROM and subword tables and the
    program table. -/
def WritesRangeCheckedClaim : Prop :=
  ∀ {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry} {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)} {projection : RV.Instr → Option (DecoderData PooledFamily)} (_table : projection = rvPooledDecoderFields ∨ projection = NonDeterminism.Pooled.rvDecoderFields) (_inputs : RVPooledBootInputs trace initial cells program inits projection) (_accepted : Accepted trace) (_decoded : RVPooledDecoded trace program),
    ∀ row ∈ trace.rows, WritesRangeChecked row.memorySteps

/-- The assumptions of `WritesRangeCheckedClaim` can be met, by a trace with a row that has ports, all of whose reads
    are bounded (so the conclusion's premise holds too). -/
def WritesRangeCheckedSatisfiableClaim : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout))
    (projection : RV.Instr → Option (DecoderData PooledFamily)),
    (projection = rvPooledDecoderFields ∨ projection = NonDeterminism.Pooled.rvDecoderFields) ∧
    RVPooledBootInputs trace initial cells program inits projection ∧ Accepted trace ∧
    RVPooledDecoded trace program ∧
    ∃ row ∈ trace.rows, row.memorySteps ≠ [] ∧ ∀ step ∈ row.memorySteps, step.1.word.Bounded

end Airbender.Trace

namespace Airbender.UnifiedReduced
open Trace

/-- The unified reduced machine: every row of an accepted trace has range-checked writes (its own constraints). -/
def WritesRangeCheckedClaim : Prop :=
  ∀ {trace : UnifiedTrace babyBearModulus} (_accepted : Accepted trace),
    ∀ row ∈ trace.rows, WritesRangeChecked row.memorySteps

/-- The assumption of `WritesRangeCheckedClaim` can be met, by a trace with a row that has ports, all of whose reads
    are bounded. -/
def WritesRangeCheckedSatisfiableClaim : Prop :=
  ∃ trace : UnifiedTrace babyBearModulus, Accepted trace ∧
    ∃ row ∈ trace.rows, row.memorySteps ≠ [] ∧ ∀ step ∈ row.memorySteps, step.1.word.Bounded

end Airbender.UnifiedReduced

namespace Airbender.Delegation
open Trace

/-- The four delegation workers: every row of an accepted pool has range-checked writes. The tables, `rounds` and
    `keccakActive` are the fields of `RVOperationInputs` (the modeled tables; the Blake2s round's round mask and the
    Keccak row's execute flag, caller/padding conditions awaiting request binding). -/
def WritesRangeCheckedClaim : Prop :=
  ∀ {data : MemoryData babyBearModulus} {control : Fin 4096 → Vector Nat 6} (_accepted : MemoryAccepted data) (_tables : data.setup = modeledSetup control) (_rounds : ∀ row ∈ data.rows, row.family = .blakeRound → ∃ round, Blake2Round.Memory.RoundMask row.assignment round) (_keccakActive : ∀ row ∈ data.rows, row.family = .keccak → row.assignment Keccak.Variables.execute = 1),
    ∀ row ∈ data.rows, WritesRangeChecked row.memorySteps

/-- The assumptions of `WritesRangeCheckedClaim` can be met by a pool with a row that has ports, all of whose reads
    are bounded (so the conclusion's premise holds too). -/
def WritesRangeCheckedSatisfiableClaim : Prop :=
  ∃ (data : MemoryData babyBearModulus) (control : Fin 4096 → Vector Nat 6), MemoryAccepted data ∧
    data.setup = modeledSetup control ∧
    (∀ row ∈ data.rows, row.family = .blakeRound → ∃ round, Blake2Round.Memory.RoundMask row.assignment round) ∧
    (∀ row ∈ data.rows, row.family = .keccak → row.assignment Keccak.Variables.execute = 1) ∧
    ∃ row ∈ data.rows, row.memorySteps ≠ [] ∧ ∀ step ∈ row.memorySteps, step.1.word.Bounded

end Airbender.Delegation

namespace Airbender.Keccak.Split.Native
open Trace

/-- The split Keccak workers: every active row of an accepted pool has range-checked writes. -/
def WritesRangeCheckedClaim : Prop :=
  ∀ {data : MemoryData babyBearModulus} (_accepted : MemoryAccepted data) (_active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1),
    ∀ row ∈ data.rows, WritesRangeChecked row.memorySteps

/-- The assumptions of `WritesRangeCheckedClaim` can be met by a pool with a row that has ports, all of whose reads
    are bounded (so the conclusion's premise holds too). -/
def WritesRangeCheckedSatisfiableClaim : Prop :=
  ∃ data : MemoryData babyBearModulus, MemoryAccepted data ∧
    (∀ row ∈ data.rows, row.assignment row.columns.execute = 1) ∧
    ∃ row ∈ data.rows, row.memorySteps ≠ [] ∧ ∀ step ∈ row.memorySteps, step.1.word.Bounded

end Airbender.Keccak.Split.Native

namespace Airbender.InitsTeardowns
open Trace

/-- The inits/teardowns sets, any layout: every `Init` tuple writes the zero word. -/
def WritesRangeCheckedClaim : Prop :=
  ∀ {p : Nat} {layout : Layout} (w : Witness p layout), ∀ token ∈ w.initTokens, token.word.Bounded

/-- `WritesRangeCheckedClaim` is about some `Init` tuple: an instance of the standalone circuit has one. -/
def WritesRangeCheckedSatisfiableClaim : Prop :=
  ∃ w : Witness babyBearModulus importedLayout, ∃ token, token ∈ w.initTokens

end Airbender.InitsTeardowns
