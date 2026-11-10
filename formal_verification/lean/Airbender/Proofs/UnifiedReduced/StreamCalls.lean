import Airbender.Review.Trace.UnifiedReduced.StreamCalls

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Airbender.Trace Reference.RiscV.Sail Reference.Sail

/-- The added external-read/write CSR metadata cannot conflict with the
ordinary, TRIADD/XORROT or modular metadata registry. -/
theorem decoder_registries_disjoint (instruction : SailRV32.instruction) :
    UnifiedReduced.Modular.decoderFields instruction = none ∨
      Caller.Stream.externalDecoderFields instruction = none := by
  cases instruction <;>
    simp [Caller.Stream.externalDecoderFields, UnifiedReduced.Modular.decoderFields,
      UnifiedReduced.Mixed.decoderFields, UnifiedReduced.Modular.mopDecoderFields,
      UnifiedReduced.customDecoderFields, UnifiedReduced.decoderFields]
  case CSRReg args =>
    rcases args with ⟨csr, rs1, rd, operation⟩
    left
    simp [Trace.decoderFields, JumpBranchSlt.decoderFields, ShiftBinop.decoderFields]

/-- The external input CSR and the currently modeled custom-call CSRs have
different public addresses. -/
theorem external_callers_disjoint (instruction : SailRV32.instruction) :
    Caller.Stream.externalDecoderFields instruction = none ∨
      Delegation.Caller.decoderFields instruction = none := by
  cases instruction <;>
    simp [Caller.Stream.externalDecoderFields, Delegation.Caller.decoderFields]
  case CSRReg args =>
    rcases args with ⟨csr, rs1, rd, operation⟩
    by_cases selected : csr = 0x7C0
    · right
      cases operation <;> cases rs1 <;> cases rd <;>
        simp [selected]
    · left
      cases operation <;>
        simp
      intro equal
      exact (selected equal).elim

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Every existing unified modular instruction is a noncaller step of the
stream-aware machine relation, with unchanged external-input position. -/
theorem modular_step {program : List (Trace.ProgramEntry UnifiedFamily)}
    {before after : State} (stream : List (BitVec 32)) (position : Nat)
    (callers : List Delegation.Caller.ProgramEntry)
    (step : UnifiedReduced.Modular.Step program before after) :
    Caller.Stream.Step stream program callers (before, position) (after, position) := by
  left
  rcases step with ⟨entry, member, source, pc, original, clause, execution⟩
  refine ⟨entry, member, ?_, pc, original, ?_, execution⟩
  · exact ⟨source.bytes, source.decoded, by
      simp [Caller.Stream.decoderFields, source.fields]⟩
  · simp [Caller.Stream.clauseFor, clause]

/-- Existing complete caller retirement is admitted without consuming an
external-input word. -/
theorem caller_step {program : List (Trace.ProgramEntry UnifiedFamily)}
    {callers : List Delegation.Caller.ProgramEntry} {before after : State}
    (stream : List (BitVec 32)) (position : Nat)
    {entry : Delegation.Caller.ProgramEntry} (member : entry ∈ callers)
    (source : entry.SourceWith before Delegation.Caller.decoderFields)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok entry.pc before)
    (retirement : Caller.FullRetirement entry.data.family before after) :
    Caller.Stream.Step stream program callers (before, position) (after, position) := by
  right
  exact ⟨rfl, entry, member, source, pc, retirement⟩

end Airbender.UnifiedReduced.Caller.Stream.Proofs
