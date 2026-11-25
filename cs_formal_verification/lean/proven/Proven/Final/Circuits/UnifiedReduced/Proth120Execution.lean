module
public import Proven.UnifiedReduced.Proth120.ModularExecution
public import Proven.UnifiedReduced.RV.Dispatch

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Arithmetic Trace

/-- A row fetched from the wrap ROM implements one RV32 step, including the wrap's RAM boundary
    and all four BabyBear emulation branches. -/
theorem row_soundness : RowSoundnessClaim := by
  intro cells epoch w before after inputs
  obtain ⟨i, data, decoded, fields, query⟩ := inputs.decoded
  let entry : UnifiedReduced.RVProgramEntry := ⟨before.pc, _root_.RV.read before.rom before.pc 4, data⟩
  have native : decoderQuery w = entry.query := query
  have result : UnifiedReduced.Standard.Proofs.RV.RowStepAt .proth120 w before after i := by
    rcases decoded_cases fields with ordinary | ⟨op, r1, r2, rd, rfl, md⟩
    · apply UnifiedReduced.Standard.Proofs.RV.row_step_field .proth120 (entry := entry) (cells := cells) (epoch := epoch) (words := ROM.wordsRV before)
      exact ⟨full_setup_holds inputs.constraints, inputs.active, native, ordinary, decoded, rfl,
        inputs.fetch.1, inputs.bounded.1, inputs.bounded.2.1, inputs.bounded.2.2, inputs.history, inputs.aligned, rfl⟩
    · exact modular_step inputs op r1 r2 rd entry rfl md native
  obtain ⟨next, result, agreement⟩ := result
  refine ⟨next, ?_, agreement⟩
  rw [show UnifiedReduced.Standard.Profile.proth120.romLimbs * 65536 = romEnd by decide] at result
  simpa [step, inputs.fetch.1, inputs.fetch.2, decoded] using result

end Airbender.UnifiedReduced.Proth120
