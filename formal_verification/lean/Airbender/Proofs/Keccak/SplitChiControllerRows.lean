import Airbender.Proofs.Keccak.SplitControlBinding
import Airbender.Review.Circuits.Keccak.SplitCall

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000

/-- The retained controller row determines its exact blessed micro-call. -/
def chi5ControllerIndex (i : Fin chi5Control.length) : Fin 361 :=
  ⟨15 * ((i.val - 1) / 5) + 10 + (i.val - 1) % 5, by
    have bound := i.isLt
    change i.val < 121 at bound
    omega⟩

/-- Every active retained controller row contains the original schedule and slots. -/
theorem chi5_controller_schedule : ∀ i : Fin chi5Control.length,
    (chi5Control.row i)[1] = 1 →
      kindAt (chi5ControllerIndex i).val = .chi5 ∧
      (chi5Control.row i)[0] = (controlAt (chi5ControllerIndex i).val : Int) ∧
      (chi5Control.row i)[2] = (bump (controlAt (chi5ControllerIndex i).val) : Int) ∧
      (∀ lane : Fin 5, (chi5Control.row i)[3 + lane.val] =
        ((Call.slots (chi5ControllerIndex i))[lane.val].val : Int)) ∧
      (chi5Control.row i)[8] = (((chi5ControllerIndex i).val % 5 : Nat) : Int) := by
  decide +kernel

/-- Tagged native table membership binds an active chi5 row to the original schedule. -/
theorem chi5_generic_controller_schedule [Fact babyBearModulus.Prime]
    (row : Vector (ZMod babyBearModulus) 11)
    (sound : (chi5Generic.table "Airbender.SplitChi5Generic").toRaw.Soundness #[] row)
    (tag : row[10] = 66) (active : row[1] = 1) :
    ∃ index : Fin 361, kindAt index.val = .chi5 ∧
      row[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      row[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (∀ lane : Fin 5, row[3 + lane.val] = ((Call.slots index)[lane.val].val : ZMod babyBearModulus)) ∧
      row[8] = ((index.val % 5 : Nat) : ZMod babyBearModulus) := by
  have member := chi5_generic_controller_sound row sound tag
  change ∃ i : Fin chi5Control.length,
    row = (chi5Control.row i).map (fun value : Int => (value : ZMod babyBearModulus)) at member
  obtain ⟨i, rfl⟩ := member
  have enabled : (chi5Control.row i)[1] = 1 := by
    rcases chi5_controller_execute i with zero | one
    · simp [zero] at active
    · exact one
  obtain ⟨kind, before, after, slots, iteration⟩ := chi5_controller_schedule i enabled
  refine ⟨chi5ControllerIndex i, kind, ?_, ?_, ?_, ?_⟩
  · simpa only [Vector.getElem_map, Int.cast_natCast] using
      congrArg (fun value : Int => (value : ZMod babyBearModulus)) before
  · simpa only [Vector.getElem_map, Int.cast_natCast] using
      congrArg (fun value : Int => (value : ZMod babyBearModulus)) after
  · intro lane
    simpa only [Vector.getElem_map, Int.cast_natCast] using
      congrArg (fun value : Int => (value : ZMod babyBearModulus)) (slots lane)
  · simpa only [Vector.getElem_map, Int.cast_natCast] using
      congrArg (fun value : Int => (value : ZMod babyBearModulus)) iteration

end Airbender.Keccak.Split.Native.Fixed.Proofs
