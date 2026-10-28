import Airbender.Review.Trace.Modular.ExternalCalls

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Trace Reference.RiscV.Sail Reference.Sail

/-- Pooled arithmetic/modular/external metadata and delegated caller metadata
use disjoint CSR addresses. -/
theorem decoder_registries_disjoint (instruction : SailRV32.instruction) :
    AddSub.Modular.External.decoderFields instruction = none ∨
      Delegation.Caller.decoderFields instruction = none := by
  cases instruction <;>
    simp [Delegation.Caller.decoderFields]
  case CSRReg args =>
    rcases args with ⟨csr, rs1, rd, operation⟩
    by_cases external : csr = 0x7C0
    · right
      cases operation <;> cases rs1 <;> cases rd <;>
        simp [external]
    · left
      cases operation <;> cases rs1 <;> cases rd <;>
        simp [AddSub.Modular.External.decoderFields,
          AddSub.Modular.External.arithmeticDecoderFields,
          NonDeterminism.decoderFields,
          Trace.pooledDecoderFields, Trace.decoderFields,
          JumpBranchSlt.decoderFields, MulDiv.decoderFields,
          ShiftBinop.decoderFields, SubwordMemory.decoderFields]
      intro equal
      exact (external equal).elim

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Existing pooled modular/external steps lift without changing the stream
position or their original Sail/custom clause. -/
theorem modular_external_step (allowed : Delegation.Family → Prop)
    (callers : List Delegation.Caller.ProgramEntry)
    {stream : List (BitVec 32)} {program : List PooledProgramEntry}
    {before after : State × Nat}
    (step : AddSub.Modular.External.Step stream program before after) :
    Caller.Step allowed stream program callers before after :=
  Or.inl step

/-- A complete caller retirement is admitted at a fixed stream position when
its family belongs to the public machine registry. -/
theorem caller_step (allowed : Delegation.Family → Prop)
    {stream : List (BitVec 32)} {program : List PooledProgramEntry}
    {callers : List Delegation.Caller.ProgramEntry}
    {before after : State} {position : Nat}
    {entry : Delegation.Caller.ProgramEntry} (member : entry ∈ callers)
    (family : allowed entry.data.family)
    (source : entry.SourceWith before Delegation.Caller.decoderFields)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok entry.pc before)
    (retirement : UnifiedReduced.Caller.FullRetirement entry.data.family before after) :
    Caller.Step allowed stream program callers (before, position) (after, position) := by
  right
  exact ⟨rfl, entry, member, family, source, pc, retirement⟩

end Airbender.AddSub.Modular.External.Caller.Proofs
