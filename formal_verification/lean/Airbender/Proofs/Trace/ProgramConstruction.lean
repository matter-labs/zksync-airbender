import Airbender.Review.Helpers.Decoder.Program

namespace Airbender.Trace.Proofs
set_option warningAsError true

/-- Construct an entry from established observations, keeping the concrete
    machine state out of the decoder computation. -/
theorem program_entry_run_of_reads {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (pc bits : BitVec 32)
    (decoded : SailRV32.instruction) (data : DecoderData Kind)
    (read : (Cell.ram pc).read before = .ok bits before)
    (decode : Reference.Sail.run (SailRV32.Functions.encdec_backwards bits) before =
      .ok decoded before)
    (fields : projection decoded = some data) :
    programEntryRunWith projection before pc = some ⟨pc, bits, decoded, data⟩ := by
  simp only [programEntryRunWith, read, decode, fields, bind, Option.bind, pure]

/-- A singleton public image reuses the same observed byte/decoder facts. -/
theorem program_image_run_singleton_of_reads {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (entry : ProgramEntry Kind)
    (read : (Cell.ram entry.pc).read before = .ok entry.bits before)
    (decode : Reference.Sail.run (SailRV32.Functions.encdec_backwards entry.bits) before =
      .ok entry.instruction before)
    (fields : projection entry.instruction = some entry.data) :
    programImageRunWith projection before [entry.pc] = some [entry] := by
  have built := program_entry_run_of_reads projection before entry.pc entry.bits
    entry.instruction entry.data read decode fields
  rw [programImageRunWith, List.mapM_cons, built, List.mapM_nil]
  rfl

end Airbender.Trace.Proofs
