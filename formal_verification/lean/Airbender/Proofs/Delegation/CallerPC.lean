import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Delegation.Decoder
import Airbender.Proofs.AddSub.PC
import Airbender.Proofs.Sail.PC

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem query_pc (hp : FieldCapacity.NoWrap p 65536) {w : Nat → ZMod p} {entry : ProgramEntry}
    (equal : nativeQuery w = query entry) : initialPC w = Word.ofBitVec entry.pc := by
  have low := congrArg (fun values : Vector (ZMod p) 9 => values[0]) equal
  have high := congrArg (fun values : Vector (ZMod p) 9 => values[1]) equal
  change w 0 = ((Word.ofBitVec entry.pc).lo : ZMod p) at low
  change w 1 = ((Word.ofBitVec entry.pc).hi : ZMod p) at high
  change (⟨(w 0).val, (w 1).val⟩ : Word) = Word.ofBitVec entry.pc
  exact Trace.Proofs.word_of_pc_query hp low high

theorem pc_binding [Fact p.Prime] (hp : FieldCapacity.NoWrap p 196608)
    (inverse : SerializedInverse.Limb16 p)
    {before : State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (image : programImage before addresses = some program)
    (member : (decoderTable program).Contains #[] (nativeQuery w)) :
    PCBinding w before program := by
  obtain ⟨entry, present, source, equal⟩ := public_source image member
  have initial := query_pc (by omega) equal
  have mapping : AddSub.PCMapping (initialPC w) (finalPC w) w := by
    constructor
    · change w 0 = ((w 0).val : ZMod p)
      exact (ZMod.natCast_zmod_val _).symm
    · change w 1 = ((w 1).val : ZMod p)
      exact (ZMod.natCast_zmod_val _).symm
    · rfl
    · rfl
  have result := AddSub.Proofs.pc_successor hp inverse constraints mapping
    (initial.symm ▸ Word.ofBitVec_bound entry.pc)
  refine ⟨⟨entry, present, source, initial⟩, AddSub.Proofs.pc_bounds constraints mapping, result.2.2, ?_⟩
  intro state read
  have prepare := initialize_next_pc read
  rw [run_bind_of_ok _ _ _ _ _ prepare]
  have finish := tick_pc_run (state := { state with regs := state.regs.insert .nextPC ((initialPC w).toBitVec + 4) })
    (pc := (initialPC w).toBitVec + 4) (by simp)
  simpa only [result.2.2] using finish

end Airbender.Delegation.Caller.Proofs
