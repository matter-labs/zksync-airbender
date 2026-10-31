import Airbender.Proofs.Trace.Program

namespace Airbender.Compiler.PublicProgram
open Airbender Airbender.Trace
set_option warningAsError true

/-- An actual Sail source certificate also constructs the stateful public
program interface. In particular, pure decoding is never substituted for an
unproved stateful decoder result. -/
theorem entry_run {Kind : Type} {before : Reference.RiscV.Sail.State}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {entry : ProgramEntry Kind} (source : entry.SourceWith before projection) :
    programEntryRunWith projection before entry.pc = some entry := by
  unfold programEntryRunWith
  simp only [source.bytes, bind, Option.bind, source.decoded, source.fields]
  rfl

theorem image_run {Kind : Type} {before : Reference.RiscV.Sail.State}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    (program : List (ProgramEntry Kind))
    (sources : ∀ entry ∈ program, entry.SourceWith before projection) :
    programImageRunWith projection before (program.map ProgramEntry.pc) = some program := by
  induction program with
  | nil => rfl
  | cons entry rest ih =>
    have first := entry_run (sources entry (by simp))
    have tail := ih (fun item member => sources item (by simp [member]))
    simp only [programImageRunWith, List.map_cons, List.mapM_cons, first,
      bind, Option.bind, tail]
    rfl

end Airbender.Compiler.PublicProgram
