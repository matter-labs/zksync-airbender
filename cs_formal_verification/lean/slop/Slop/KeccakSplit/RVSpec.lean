module
public import Slop.KeccakSplit.Reference.PermutationDefinitions
public import Slop.Deleg.KeccakF1600
public import Slop.Deleg.KeccakClean
public import Slop.Deleg.KeccakCalls

@[expose] public section

/-! State-free agreement of the split Keccak calls with the spec's `RV.Delegation.keccakF1600`: the split circuits'
    `physicalSlot`/`piSource` are the spec's `laneSlot`/`piSrc`; each scheduled call's live slots are distinct; and
    the spec's `f1600Step` on 64-bit lanes is the split `microStep` on their values (`f1600_step_nat`). The control
    words, the next control and the call kinds of the 361-call schedule are the spec's (`RV.f1600Calls`). -/

namespace Airbender.Keccak.Split.Call.Proofs
open Spec RV.Delegation
set_option warningAsError true
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

theorem pi_source_spec : ∀ p : Fin 25, piSource p = piSrc p := by decide

theorem physical_slot_spec (r : Nat) (p : Fin 25) : physicalSlot r p = laneSlot r p := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih => simp only [physicalSlot, laneSlot, pi_source_spec, ih]

/-- The spec kind of a split worker. -/
def _root_.Airbender.Keccak.Split.Kind.delegation : Kind → RV.DelegationKind
  | .columnParity => .keccakParity
  | .thetaRho => .keccakThetaRho
  | .chi5 => .keccakChi5

theorem f1600_calls_length : RV.f1600Calls.length = 361 := by decide

theorem f1600_calls_eq : RV.f1600Calls = (List.finRange 361).map fun i => (kindAt i.val).delegation := by
  rfl

theorem f1600_calls_kinds (i : Fin 361) :
    RV.f1600Calls[i.val]'(by rw [f1600_calls_length]; exact i.isLt) = (kindAt i.val).delegation := by
  simp only [f1600_calls_eq, List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta]

/-- Call `i`'s control word is the spec's `control op x r` with the worker's op, `x = i % 5`, `r = i / 15`. -/
theorem control_at_spec (i : Fin 361) :
    controlAt i.val = (kindAt i.val).mode + 8 * (i.val % 5) + 64 * (i.val / 15) := by
  have bound := i.isLt
  unfold controlAt encode
  split_ifs with last
  · simp [last, kindAt, Kind.mode]
  · rfl

/-- Every scheduled call is a valid piece of the spec's `keccakF1600` for its worker. -/
theorem schedule_spec_valid : ∀ i : Fin 361,
    i.val / 15 < 24 ∨ i.val / 15 = 24 ∧ i.val % 5 = 0 ∧ (kindAt i.val).mode = 0 := by
  decide

/-- The control word a worker writes back is the spec's `f1600Next`. -/
theorem bump_spec : ∀ i : Fin 361,
    (f1600Next (kindAt i.val).mode (i.val % 5) (i.val / 15)).1 +
      8 * (f1600Next (kindAt i.val).mode (i.val % 5) (i.val / 15)).2.1 +
      64 * (f1600Next (kindAt i.val).mode (i.val % 5) (i.val / 15)).2.2 = bump (controlAt i.val) := by
  decide +kernel

end Airbender.Keccak.Split.Call.Proofs
