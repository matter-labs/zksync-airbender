import Airbender.Proofs.AddSub.NonDeterminism
import Airbender.Proofs.UnifiedReduced.Retirement
import Airbender.Proofs.UnifiedReduced

namespace Airbender.UnifiedReduced.ExternalInput.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

/-- Derive the external read's PC update from the current unified circuit.
The supplied stream slot remains the explicit external input boundary. -/
theorem read_spec {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 524288)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) (active : w 4 = 1)
    {entry : ProgramEntry} {rd : BitVec 5}
    (metadata : entry.data = ⟨.machine, 0, 0, rd, ⟨0, 0⟩, 256, 0⟩)
    (query : decoderQuery w = entry.query)
    (stream : List (BitVec 32)) (position : Nat) (before : State)
    (port : stream[position]? = some (Control.destination w).toBitVec) :
    AddSub.NonDeterminism.readSpec
      ⟨stream, position, .Regidx rd, Control.initialPC w,
        retiredState before (Control.initialPC w).toBitVec⟩
      ⟨Control.destination w, Control.finalPC w⟩ := by
  have small : entry.data.mask < 524288 := by
    rw [metadata]
    change 256 < 524288
    decide +kernel
  have flags := UnifiedReduced.Proofs.decoder_selectors hp core small query
  have f10 := flags 10
  have f11 := flags 11
  have f12 := flags 12
  have f13 := flags 13
  norm_num [metadata, importedConstraintsDecoderColumns, Nat.testBit,
    Nat.shiftRight_eq_div_pow] at f10 f11 f12 f13
  have initial : (Control.initialPC w).Bounded := by
    have value := native_query_pc_word (p := p) (by dsimp [limbBase]; omega) query
    change Control.initialPC w = Word.ofBitVec entry.pc at value
    exact value.symm ▸ Word.ofBitVec_bound entry.pc
  have next := UnifiedReduced.Proofs.pc_successor (p := p) (by omega)
    core active ⟨f10, f11, f12, f13⟩
    (initial := Control.initialPC w) (final := Control.finalPC w)
    ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ initial
  refine ⟨(Control.destination w).toBitVec, port,
    UnifiedReduced.Proofs.destination_bounds core, ?_⟩
  apply Reference.RiscV.Sail.retire_of_destination (retired_state_pc before _) next.2.2
  obtain ⟨after, write⟩ := Reference.RiscV.Sail.write_success (.Regidx rd)
    (Control.destination w).toBitVec
    { retiredState before (Control.initialPC w).toBitVec with
      regs := (retiredState before (Control.initialPC w).toBitVec).regs.insert
        .nextPC (Control.finalPC w).toBitVec }
  have effect := run_bind_of_ok _
    (fun (_ : Unit) => (pure SailRV32.Functions.RETIRE_SUCCESS : SailRV32.SailM _))
    _ _ _ write
  exact ⟨after, effect, effect⟩

/-- Combine the external read with the exact native register history.
No expected register result or private selector premise is added. -/
theorem read_execution {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 524288)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) (active : w 4 = 1)
    {entry : ProgramEntry} {rd : BitVec 5}
    (metadata : entry.data = ⟨.machine, 0, 0, rd, ⟨0, 0⟩, 256, 0⟩)
    (query : decoderQuery w = entry.query)
    (stream : List (BitVec 32)) (position : Nat)
    (port : stream[position]? = some (Control.destination w).toBitVec)
    (epoch : Nat) {cells : List Cell} {before after : State}
    (history : SailHistory cells
      (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    run (normalStep (writeResult (.Regidx rd) (Control.destination w)))
      (retiredState before (Control.initialPC w).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (retiredState after (Control.finalPC w).toBitVec) := by
  obtain ⟨response, responsePort, _, final, normal, projected⟩ :=
    read_spec hp core active metadata query stream position before port
  have responseEq := Option.some.inj (port.symm.trans responsePort)
  rw [← responseEq] at normal
  have small : entry.data.mask < 524288 := by
    rw [metadata]
    change 256 < 524288
    decide +kernel
  have flag := UnifiedReduced.Proofs.decoder_selectors hp core small query 18
  have noStore : w 29 = 0 := by
    simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit,
      Nat.shiftRight_eq_div_pow] using flag
  have index := (native_query_indices (p := p) (by dsimp [limbBase]; omega) query).2.2
  rw [metadata] at index
  have effects := UnifiedReduced.Proofs.register_effects core noStore index epoch
    ⟨Control.destination w, Control.finalPC w⟩ rfl history
  have same := (EStateM.Result.ok.inj (projected.symm.trans effects)).2
  rw [same] at normal
  simpa [writeResult] using normal

end Airbender.UnifiedReduced.ExternalInput.Proofs
