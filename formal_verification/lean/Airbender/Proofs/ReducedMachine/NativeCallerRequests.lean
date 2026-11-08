import Airbender.Review.Circuits.ReducedMachine.CallerRequests
import Airbender.Proofs.ReducedMachine.NativeSelectors
import Airbender.Proofs.ReducedMachine.NativeCSRCallerClock
import Airbender.Proofs.ReducedMachine.NativeActiveWorkerClocks

namespace Airbender.NativeCallerRequestProofs
open Airbender.NativeCallerRequests Airbender.Verification Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Whole arithmetic window calculation BEFORE concrete mask instantiation. -/
theorem packed_bit (whole low bit high : Nat) (lower : low < 128) (binary : bit < 2)
    (packed : whole = low + 128*bit + 256*high) : whole / 128 % 2 = bit := by omega

/-- Actual unscaled request equations, without an instruction-mask or execute
    premise. Native oracle factors and supported-selector relation remain. -/
theorem relations {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) :
    w 24 * w 64 = w 24 ∧ w 92 = w 24*w 65 ∧ w 93 = w 36*w 92 ∧ w 94 = w 9*w 92 ∧
      w 90*w 65 = 0 ∧ w 91*w 65 = 0 := by
  have e68 := assertion_of_holds holds ⟨68,by change 68 < 117; decide⟩
  have e69 := assertion_of_holds holds ⟨69,by change 69 < 117; decide⟩
  have e70 := assertion_of_holds holds ⟨70,by change 70 < 117; decide⟩
  have e71 := assertion_of_holds holds ⟨71,by change 71 < 117; decide⟩
  have e72 := assertion_of_holds holds ⟨72,by change 72 < 117; decide⟩
  have e73 := assertion_of_holds holds ⟨73,by change 73 < 117; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e68 e69 e70 e71 e72 e73
  exact ⟨by linear_combination -e68,by linear_combination -e69,by linear_combination -e70,
    by linear_combination -e71,mul_eq_zero.mpr e72,mul_eq_zero.mpr e73⟩

theorem mask_bit {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) :
    csrMaskBit w = (w 24).val := by
  have packed := Airbender.ReducedMachine.NativeSelectorProofs.packed holds
  have b0 := Airbender.ReducedMachine.NativeSelectorProofs.bit_bounds holds ⟨0,by decide⟩
  have b1 := Airbender.ReducedMachine.NativeSelectorProofs.bit_bounds holds ⟨1,by decide⟩
  have b2 := Airbender.ReducedMachine.NativeSelectorProofs.bit_bounds holds ⟨2,by decide⟩
  have b3 := Airbender.ReducedMachine.NativeSelectorProofs.bit_bounds holds ⟨3,by decide⟩
  have b4 := Airbender.ReducedMachine.NativeSelectorProofs.bit_bounds holds ⟨4,by decide⟩
  have b5 := Airbender.ReducedMachine.NativeSelectorProofs.bit_bounds holds ⟨5,by decide⟩
  have b6 := Airbender.ReducedMachine.NativeSelectorProofs.bit_bounds holds ⟨6,by decide⟩
  have b7 := Airbender.ReducedMachine.NativeSelectorProofs.bit_bounds holds ⟨7,by decide⟩
  change (w 17).val ≤ 1 at b0
  change (w 18).val ≤ 1 at b1
  change (w 19).val ≤ 1 at b2
  change (w 20).val ≤ 1 at b3
  change (w 21).val ≤ 1 at b4
  change (w 22).val ≤ 1 at b5
  change (w 23).val ≤ 1 at b6
  change (w 24).val ≤ 1 at b7
  let low := (w 17).val+2*(w 18).val+4*(w 19).val+8*(w 20).val+16*(w 21).val+32*(w 22).val+64*(w 23).val
  let high := (w 25).val+2*(w 26).val+4*(w 27).val+8*(w 28).val+16*(w 29).val+32*(w 30).val+
    64*(w 31).val+128*(w 32).val+256*(w 33).val+512*(w 34).val
  have lower : low < 128 := by dsimp [low]; omega
  have binary : (w 24).val < 2 := by omega
  have same : (w 12).val = low+128*(w 24).val+256*high := by dsimp [low,high]; omega
  exact packed_bit _ low _ high lower binary same

theorem body {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : RowEffects w := by
  have source := relations holds
  have packed := mask_bit holds
  have bounded : (w 24).val ≤ 1 := by
    simpa using Airbender.ReducedMachine.NativeSelectorProofs.bit_bounds holds ⟨7,by decide⟩
  have oneVal : (1 : F).val = 1 := by decide +kernel
  have bit : w 24 = 0 ∨ w 24 = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp bounded with zero | one
    · left; apply ZMod.val_injective; simpa using zero
    · right; apply ZMod.val_injective; simpa only [oneVal] using one
  have multiplicity : (csrRequest w).multiplicity = w 24*w 65 := source.2.1
  have kind : (csrRequest w).kind = w 9*(csrRequest w).multiplicity := source.2.2.2.1
  have offset : (csrRequest w).offsetHigh = some (w 36*(csrRequest w).multiplicity) := congrArg some source.2.2.1
  have requested : (csrRequest w).multiplicity ≠ 0 ↔ w 24 = 1 ∧ w 65 ≠ 0 := by
    rw [multiplicity]
    constructor
    · intro present
      have both := mul_ne_zero_iff.mp present
      exact ⟨bit.elim (fun zero => False.elim (both.1 zero)) id,both.2⟩
    · rintro ⟨enabled,delegated⟩
      simpa [enabled] using delegated
  refine ⟨bit,packed,multiplicity,kind,offset,rfl,by rw [multiplicity]; exact mul_eq_zero,requested,?_,?_⟩
  · intro disabled
    have selector : w 24 = 0 := by
      apply ZMod.val_injective
      simpa only [ZMod.val_zero] using packed.symm.trans disabled
    have zero : w 92 = 0 := by simpa [selector] using source.2.1
    have high : w 93 = 0 := by simpa [zero] using source.2.2.1
    have code : w 94 = 0 := by simpa [zero] using source.2.2.2.1
    change (⟨w 92,w 94,some (w 93),3⟩ : CSRRequest) = _
    simp [zero,high,code]
  · intro present
    obtain ⟨enabled,delegated⟩ := requested.mp present
    have supported : w 64 = 1 := by simpa [enabled] using source.1
    have low : w 90 = 0 := (mul_eq_zero.mp source.2.2.2.2.1).resolve_right delegated
    have high : w 91 = 0 := (mul_eq_zero.mp source.2.2.2.2.2).resolve_right delegated
    exact ⟨enabled,by simpa only [enabled,oneVal] using packed,supported,by simp [csrOracleWord,low,high]⟩

/-- Full source acceptance on the SAME actual finite main list, sampled BEFORE
    any execution/opcode/request filtering. No supplied row/list equality. -/
theorem all_rows {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) : Effects proofs := by
  have source : ∀ proof ∈ Airbender.NativeInitializationBatch.mainProofs proofs, ∀ i < callerAuxiliaryLayout.traceLength-1,
      RowEffects (proof.rows i) := by
    intro proof member i bound
    obtain ⟨origin,present,rfl⟩ := List.mem_map.mp member
    exact body ((accepted.arguments.mainDelegation origin.main (List.mem_map.mpr ⟨origin,present,rfl⟩)).body i bound)
  exact Airbender.NativeActiveWorkerClockProofs.sampled_property
    (Airbender.NativeInitializationBatch.mainProofs proofs) (fun proof => proof.rows)
    (callerAuxiliaryLayout.traceLength-1) RowEffects source

/-- Generic duplicate-preserving clock translation BEFORE native rows. -/
theorem translated_unique {A : Type} (rows : List A) (clock caller : A → Nat)
    (same : ∀ row ∈ rows, caller row = clock row+3) (unique : (rows.map clock).Nodup) :
    (rows.map caller).Nodup := by
  have identity : rows.map caller = (rows.map clock).map (fun time => time+3) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro row member
    exact same row member
  rw [identity]
  exact List.Nodup.map (fun a b equal => by omega) unique

/-- Uses only derived initial-state range/alignment, not old-read bounds or
    a fake initialized memory trace. -/
theorem row_clock (row : Trace.Row mersenne31Modulus Trace.NativeReducedFamily)
    (initial : (Trace.decodeTimestamp row.assignment row.columns.initialTime).Bounded)
    (aligned : (Trace.decodeTimestamp row.assignment row.columns.initialTime).lo % 4 = 0) :
    (Trace.timeOfPair (csrCallerObservation row).time).Bounded ∧
      (csrCallerObservation row).clock = row.clock+3 ∧ (csrCallerObservation row).clock % 4 = 3 := by
  cases row with
  | mk family w =>
    cases family
    have time := Trace.Proofs.write_time (p := mersenne31Modulus) (by decide)
      (base := Trace.rawPair w importedConstraintsTraceColumns.initialTime) initial aligned (offset := 3) (by decide)
    have actual : (Trace.timeOfPair (csrCallerObservation (.mk .reduced w)).time).Bounded ∧
        (csrCallerObservation (.mk .reduced w)).clock =
          (Trace.Row.mk .reduced w : Trace.Row mersenne31Modulus Trace.NativeReducedFamily).clock+3 := by
      change (Trace.timeOfPair (w 2+3,w 3)).Bounded ∧
        (Trace.timeOfPair (w 2+3,w 3)).value = (Trace.timeOfPair (w 2,w 3)).value+3
      exact time
    have baseAligned : (Trace.Row.mk .reduced w : Trace.Row mersenne31Modulus Trace.NativeReducedFamily).clock % 4 = 0 := by
      change (w 2).val % 4 = 0 at aligned
      change ((w 2).val+524288*(w 3).val)%4 = 0
      simp [Nat.add_mod,Nat.mul_mod,aligned]
    exact ⟨actual.1,actual.2,by omega⟩

theorem active_clocks {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    ActiveClockEffects proofs inputs := by
  have state := Airbender.NativeMainStateHistoryProofs.history embed memory pc
    (Airbender.NativeMemoryHistoryProofs.components embed memory ch pc gamma config accepted) accepted.matching
  have pointwise : ∀ row ∈ Airbender.NativeMainStateHistory.rows (Airbender.NativeInitializationBatch.mainProofs proofs),
      (Trace.timeOfPair (csrCallerObservation row).time).Bounded ∧
        (csrCallerObservation row).clock = row.clock+3 ∧ (csrCallerObservation row).clock % 4 = 3 ∧
        7 ≤ (csrCallerObservation row).clock ∧ (csrCallerObservation row).clock < terminalClock inputs := by
    intro row member
    obtain ⟨initial,aligned⟩ := state.clocks row member
    obtain ⟨bounded,value,residue⟩ := row_clock row initial aligned
    have interval := state.interval row member
    change 4 ≤ row.clock ∧ row.clock+4 ≤ terminalClock inputs at interval
    exact ⟨bounded,value,residue,by omega,by omega⟩
  exact ⟨pointwise,translated_unique _ Trace.Row.clock (fun row => (csrCallerObservation row).clock)
    (fun row member => (pointwise row member).2.1) state.unique⟩
end Airbender.NativeCallerRequestProofs
