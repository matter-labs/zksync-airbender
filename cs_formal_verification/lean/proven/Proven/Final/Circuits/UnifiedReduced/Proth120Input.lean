module
public import Human.Circuits.UnifiedReduced.Proth120Input
public import Proven.UnifiedReduced.Proth120.ModularExecution
public import Proven.UnifiedReduced.Proth120.CSRWitness

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Arithmetic Trace

/-- Native port two writes the independent stream head on a read. The NOP metadata of a write
    targets x0, so every observable register and the input stream are preserved. -/
theorem csr_row_soundness : CSRRowSoundnessClaim := by
  intro cells epoch w before after read inputs
  obtain ⟨r, _, fetched, query⟩ := inputs.decoded
  let data : DecoderData UnifiedFamily := if read then ⟨.machine, 0, 0, r, ⟨0, 0⟩, 256, 0⟩ else rvNopFields
  let entry : UnifiedReduced.RVProgramEntry := ⟨before.pc, _root_.RV.read before.rom before.pc 4, data⟩
  have native : decoderQuery w = entry.query := query
  have small : entry.data.mask < 512 := by cases read <;> simp [entry, data, rvNopFields]
  obtain ⟨_, _, _, _, _, written, finish⟩ := UnifiedReduced.Standard.Modular.Proofs.row_frame (profile := .proth120) (by decide)
    (full_setup_holds inputs.constraints) inputs.active native small rfl inputs.history
  have same := UnifiedReduced.Standard.Proofs.RV.rv_register_next written finish
  cases read
  · change _root_.RV.Same (before.setReg 0 (wordAt w 50).toBitVec).nextInstr _ at same
    have agree := ((UnifiedReduced.Standard.Proofs.RV.same_set_zero before (wordAt w 50).toBitVec).nextInstr).symm.trans same
    refine ⟨before.nextInstr, ?_, agree.1, agree.2.1, agree.2.2.1, agree.2.2.2.1, rfl⟩
    simp [step, inputs.fetch.1, inputs.fetch.2, fetched, _root_.RV.exec]
  · change _root_.RV.Same (before.setReg r (wordAt w 50).toBitVec).nextInstr _ at same
    have head := inputs.response rfl
    cases stream : before.input with
    | nil => simp [stream] at head
    | cons a rest =>
      have response : a = (wordAt w 50).toBitVec := by simpa [stream] using head
      subst a
      refine ⟨{ (before.setReg r (wordAt w 50).toBitVec).nextInstr with input := rest },
        ?_, same.1, same.2.1, same.2.2.1, same.2.2.2.1, ?_⟩
      · simp [step, inputs.fetch.1, inputs.fetch.2, fetched, _root_.RV.exec, stream]
      · simp

theorem csr_row_soundness_satisfiable : CSRRowSoundnessSatisfiableClaim := by
  exact ⟨_, _, _, _, _, true, CSRWitness.inputs true, rfl, rfl⟩

end Airbender.UnifiedReduced.Proth120
