import Human.Trace.Workers.Blake2Round.Compression
import Slop.Deleg.BlakeCall
import Slop.Blake2Round.Schedule
import Slop.Arithmetic.Word

/-! State-free agreement of the extended-BLAKE round reference (`Compression.step`) with the spec's round delegation
    (`RV.Delegation.blakeRound`, through `RV.blakeRound_mode_call`): the x12 schedule is `RV.bCtl`, and one reference
    round on 32-bit words writes exactly the spec's chaining and working words. -/

namespace Airbender.Blake2Round.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

/-- The flags of a request as the spec's three mode bits. -/
abbrev reducedOf (flags : Fin 8) : Bool := decide (flags.val % 2 = 1)
abbrev rightOf (flags : Fin 8) : Bool := decide (flags.val / 2 % 2 = 1)
abbrev compressionOf (flags : Fin 8) : Bool := decide (flags.val / 4 = 1)

theorem controlAt_toBitVec : ∀ (flags : Fin 8) (r : Fin 11),
    (controlAt flags r.val).toBitVec = RV.bCtl (reducedOf flags) (rightOf flags) (compressionOf flags) r.val := by
  decide +kernel

theorem calls_eq_nR (flags : Fin 8) : (if flags.val % 2 = 1 then 7 else 10) = RV.nR (reducedOf flags) := by
  simp only [RV.nR, reducedOf, decide_eq_true_eq]

/-- The compression-mode working vector of round 0. -/
theorem compression_v0 :
    ((Preparation.configuredIV ++ Preparation.compressionIV).map Word.toBitVec) =
      #v[Spec.configuredIV 0, Spec.configuredIV 1, Spec.configuredIV 2, Spec.configuredIV 3, Spec.configuredIV 4,
        Spec.configuredIV 5, Spec.configuredIV 6, Spec.configuredIV 7, Spec.IV 0, Spec.IV 1, Spec.IV 2, Spec.IV 3,
        Spec.IV 4 ^^^ 64#32, Spec.IV 5, Spec.IV 6 ^^^ 0xFFFFFFFF#32, Spec.IV 7] := by
  decide +kernel

theorem compression_v0_bounded : ∀ i : Fin 16, (Preparation.configuredIV ++ Preparation.compressionIV)[i].Bounded := by
  unfold Word.Bounded
  decide +kernel

theorem configuredIV_bits : Preparation.configuredIV.map Word.toBitVec = Vector.ofFn Spec.configuredIV := by
  decide +kernel

theorem configuredIV_bounded : ∀ i : Fin 8, Preparation.configuredIV[i].Bounded := by
  unfold Word.Bounded
  decide +kernel

theorem iv_bits : ∀ i : Fin 8, (Preparation.iv[i]).toBitVec = Spec.IV i := by
  decide +kernel

theorem iv_bounded : ∀ i : Fin 8, (Preparation.iv[i]).Bounded := by
  unfold Word.Bounded
  decide +kernel

theorem append_ofFn {α : Type} (xs ys : Vector α 8) :
    xs ++ ys = Vector.ofFn fun i : Fin 16 => if h : i.val < 8 then xs[i.val] else ys[i.val - 8] := by
  apply Vector.ext
  intro i bound
  rw [Vector.getElem_append, Vector.getElem_ofFn]

/-- The normal-mode working vector of round 0. -/
theorem normal_v0 (h : Vector Word 8) (e : Vector Word 16) :
    (h ++ (Preparation.iv.set 4 e[12]).set 6 e[14]).map Word.toBitVec =
      RV.blakeV0 (h.map Word.toBitVec) (e.map Word.toBitVec) := by
  rw [append_ofFn]
  apply Vector.ext
  intro i bound
  have entry (j : Fin 8) := iv_bits j
  interval_cases i <;> simp [RV.blakeV0, Vector.getElem_set, ← entry]

theorem normal_v0_bounded (h : Vector Word 8) (e : Vector Word 16)
    (hb : ∀ i : Fin 8, h[i].Bounded) (eb : ∀ i : Fin 16, e[i].Bounded) :
    ∀ i : Fin 16, (h ++ (Preparation.iv.set 4 e[12]).set 6 e[14])[i].Bounded := by
  rw [append_ofFn]
  intro i
  have hb' : ∀ j (bound : j < 8), h[j].Bounded := fun j bound => hb ⟨j, bound⟩
  have eb' : ∀ j (bound : j < 16), e[j].Bounded := fun j bound => eb ⟨j, bound⟩
  have entry : ∀ j (bound : j < 8), (Preparation.iv[j]).Bounded := fun j bound => iv_bounded ⟨j, bound⟩
  fin_cases i <;> simp [Vector.getElem_set] <;>
    first | exact hb' _ (by decide) | exact eb' _ (by decide) | exact entry _ (by decide)

theorem schedule_sigma : ∀ (r : Fin 10) (i : Fin 16),
    Fin.ofNat 16 Blake2G.Control.messageSchedule[r][i] = Spec.SIGMA r i := by
  decide +kernel

/-- Round 0 prepares the working vector; later rounds keep it. -/
theorem prepared_extended (comp right : Bool) {r : Nat} (hr : r < 10) (h : Vector Word 8)
    (e m : Vector Word 16) :
    (Preparation.step ⟨Fin.ofNat 10 r == 0, comp, right, h, e, m⟩).extended.map Word.toBitVec =
      if r = 0 then RV.bV0 comp (h.map Word.toBitVec) (e.map Word.toBitVec) else e.map Word.toBitVec := by
  by_cases r0 : r = 0
  · subst r0
    cases comp
    · simpa [Preparation.step, RV.bV0] using normal_v0 h e
    · simpa [Preparation.step, RV.bV0] using compression_v0
  · have divides : ¬ 10 ∣ r := by omega
    simp [Preparation.step, divides, r0]

theorem prepared_extended_bounded (comp right : Bool) (r : Nat) (h : Vector Word 8) (e m : Vector Word 16)
    (hb : ∀ i : Fin 8, h[i].Bounded) (eb : ∀ i : Fin 16, e[i].Bounded) :
    ∀ i : Fin 16, (Preparation.step ⟨Fin.ofNat 10 r == 0, comp, right, h, e, m⟩).extended[i].Bounded := by
  intro i
  by_cases divides : 10 ∣ r
  · cases comp
    · simpa [Preparation.step, divides] using normal_v0_bounded h e hb eb i
    · simpa [Preparation.step, divides] using compression_v0_bounded i
  · simpa [Preparation.step, divides] using eb i

theorem prepared_chaining (comp right first : Bool) (h : Vector Word 8) (e m : Vector Word 16) :
    (Preparation.step ⟨first, comp, right, h, e, m⟩).chaining.map Word.toBitVec =
      RV.bH0 comp (h.map Word.toBitVec) := by
  cases comp
  · rfl
  · simpa [Preparation.step, RV.bH0] using configuredIV_bits

theorem prepared_chaining_bounded (comp right first : Bool) (h : Vector Word 8) (e m : Vector Word 16)
    (hb : ∀ i : Fin 8, h[i].Bounded) :
    ∀ i : Fin 8, (Preparation.step ⟨first, comp, right, h, e, m⟩).chaining[i].Bounded := by
  intro i
  cases comp
  · exact hb i
  · simpa [Preparation.step] using configuredIV_bounded i

theorem prepared_message (comp right first : Bool) (h : Vector Word 8) (e m : Vector Word 16) :
    (Preparation.step ⟨first, comp, right, h, e, m⟩).message.map Word.toBitVec =
      RV.bMsg right comp (h.map Word.toBitVec) (m.map Word.toBitVec) := by
  cases comp
  · simp [Preparation.step, RV.bMsg]
  · apply Vector.ext
    intro i bound
    cases right
    · simp only [Preparation.step, Bool.not_true, Bool.false_eq_true, ↓reduceIte, RV.bMsg, Vector.getElem_map,
        Vector.getElem_ofFn]
      rw [Vector.getElem_append]
      split
      · rename_i inside
        simp only [show i < 8 by omega, ↓reduceIte, Nat.mod_eq_of_lt (show i < 8 by omega)]
      · rename_i outside
        rw [Vector.getElem_take]
        simp only [show ¬ i < 8 by omega, ↓reduceIte, Nat.mod_eq_of_lt (show i - 8 < 16 by omega),
          show i - min 8 16 = i - 8 from rfl]
    · simp only [Preparation.step, Bool.not_true, Bool.false_eq_true, ↓reduceIte, RV.bMsg, Vector.getElem_map,
        Vector.getElem_ofFn]
      rw [Vector.getElem_append]
      split
      · rename_i inside
        rw [Vector.getElem_take]
        simp only [show i < 8 by omega, ↓reduceIte, Nat.mod_eq_of_lt (show i < 16 by omega)]
      · rename_i outside
        simp only [show ¬ i < 8 by omega, ↓reduceIte, Nat.mod_eq_of_lt (show i - 8 < 8 by omega),
          show i - min 8 16 = i - 8 from rfl]

theorem prepared_message_bounded (comp right first : Bool) (h : Vector Word 8) (e m : Vector Word 16)
    (hb : ∀ i : Fin 8, h[i].Bounded) (mb : ∀ i : Fin 16, m[i].Bounded) :
    ∀ i : Fin 16, (Preparation.step ⟨first, comp, right, h, e, m⟩).message[i].Bounded := by
  intro i
  cases comp
  · simpa [Preparation.step] using mb i
  · have bound := i.isLt
    cases right
    · simp only [Preparation.step, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Fin.getElem_fin]
      rw [Vector.getElem_append]
      split
      · exact hb ⟨i.val, by omega⟩
      · rw [Vector.getElem_take]
        exact mb ⟨i.val - min 8 16, by omega⟩
    · simp only [Preparation.step, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Fin.getElem_fin]
      rw [Vector.getElem_append]
      split
      · rw [Vector.getElem_take]
        exact mb ⟨i.val, by omega⟩
      · exact hb ⟨i.val - min 8 16, by omega⟩

theorem final_round (flags : Fin 8) {r : Nat} (bound : r < RV.nR (reducedOf flags)) (h : Vector Word 8)
    (chaining : Vector Word 8) (extended : Vector Word 16) :
    Finalization.isFinal ⟨Fin.ofNat 10 r, reducedOf flags, h, chaining, extended⟩ =
      decide (r + 1 = RV.nR (reducedOf flags)) := by
  have r10 : r < 10 := by unfold RV.nR at bound; split at bound <;> omega
  have key : ∀ f : Fin 8, ∀ k : Fin 10, k.val < RV.nR (reducedOf f) →
      (Fin.ofNat 10 k.val == 9 || (Fin.ofNat 10 k.val == 6 && reducedOf f)) =
        decide (k.val + 1 = RV.nR (reducedOf f)) := by
    decide +kernel
  exact key flags ⟨r, r10⟩ bound

/-- One reference round on 32-bit words: its working words are the spec round of the spec's prepared block and
    working vector, its chaining words the spec's final fold on the last round and the state otherwise. -/
theorem step_effect (flags : Fin 8) {r : Nat} (bound : r < RV.nR (reducedOf flags))
    (h : Vector Word 8) (e m : Vector Word 16)
    (hb : ∀ i : Fin 8, h[i].Bounded) (eb : ∀ i : Fin 16, e[i].Bounded) (mb : ∀ i : Fin 16, m[i].Bounded) :
    let v' := Spec.round (RV.bMsg (rightOf flags) (compressionOf flags) (h.map Word.toBitVec) (m.map Word.toBitVec))
      (Spec.SIGMA ⟨r, by unfold RV.nR at bound; split at bound <;> omega⟩)
      (if r = 0 then RV.bV0 (compressionOf flags) (h.map Word.toBitVec) (e.map Word.toBitVec) else e.map Word.toBitVec)
    (Compression.step flags (Fin.ofNat 10 r) (h, e) m).2.map Word.toBitVec = v' ∧
    (Compression.step flags (Fin.ofNat 10 r) (h, e) m).1.map Word.toBitVec =
      if r + 1 = RV.nR (reducedOf flags) then RV.blakeFinal (RV.bH0 (compressionOf flags) (h.map Word.toBitVec)) v'
      else h.map Word.toBitVec := by
  intro v'
  have r10 : r < 10 := by unfold RV.nR at bound; split at bound <;> omega
  let prep := Preparation.step ⟨Fin.ofNat 10 r == 0, compressionOf flags, rightOf flags, h, e, m⟩
  let mixed := Specs.BLAKE3.round (prep.extended.map Word.value)
    ((Schedule.step ⟨Fin.ofNat 10 r, prep.message⟩).map Word.value)
  let ext' := mixed.map fun value => Word.ofBitVec (BitVec.ofNat 32 value)
  have shape : Compression.step flags (Fin.ofNat 10 r) (h, e) m =
      (if Finalization.isFinal ⟨Fin.ofNat 10 r, reducedOf flags, h, prep.chaining, ext'⟩ then
        (Vector.ofFn fun i : Fin 8 => prep.chaining[i].value ^^^ ext'[i.val].value ^^^ ext'[8 + i.val].value).map
          (fun value => Word.ofBitVec (BitVec.ofNat 32 value))
        else h, ext') := rfl
  have extB := prepared_extended_bounded (compressionOf flags) (rightOf flags) r h e m hb eb
  have msgB := prepared_message_bounded (compressionOf flags) (rightOf flags) (Fin.ofNat 10 r == 0) h e m hb mb
  have chainB := prepared_chaining_bounded (compressionOf flags) (rightOf flags) (Fin.ofNat 10 r == 0) h e m hb
  have mixedEq : mixed.map (BitVec.ofNat 32) =
      Spec.round (prep.message.map Word.toBitVec) (Spec.SIGMA ⟨r, r10⟩) (prep.extended.map Word.toBitVec) := by
    have values : (prep.extended.map Word.toBitVec).map BitVec.toNat = prep.extended.map Word.value := by
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_map]
      exact Word.toBitVec_toNat (extB ⟨i, hi⟩)
    have schedule : (Vector.ofFn fun i => (prep.message.map Word.toBitVec)[Spec.SIGMA ⟨r, r10⟩ i].toNat) =
        (Schedule.step ⟨Fin.ofNat 10 r, prep.message⟩).map Word.value := by
      apply Vector.ext
      intro i hi
      have index := schedule_sigma ⟨r, r10⟩ ⟨i, hi⟩
      have round : (Fin.ofNat 10 r) = ⟨r, r10⟩ := Fin.ext (by simp [Fin.val_ofNat, Nat.mod_eq_of_lt r10])
      simp only [Schedule.step, Vector.getElem_map, Vector.getElem_ofFn, round]
      have general : ∀ (s : Fin 16) (k : Nat), Fin.ofNat 16 k = s →
          (prep.message.map Word.toBitVec)[s].toNat = prep.message[Fin.ofNat 16 k].value := by
        intro s k same
        subst same
        simp only [Fin.getElem_fin, Vector.getElem_map]
        exact Word.toBitVec_toNat (msgB _)
      exact general _ _ index
    unfold Spec.round
    rw [values, schedule]
  have extBits : ext'.map Word.toBitVec = mixed.map (BitVec.ofNat 32) := by
    apply Vector.ext
    intro i hi
    simp only [ext', Vector.getElem_map, Word.ofBitVec_roundtrip]
  have extEq : ext'.map Word.toBitVec = v' := by
    rw [extBits, mixedEq, prepared_message, prepared_extended _ _ r10]
  rw [shape]
  refine ⟨extEq, ?_⟩
  dsimp only
  rw [final_round flags bound]
  by_cases last : r + 1 = RV.nR (reducedOf flags)
  · simp only [last, decide_true, ite_true]
    apply Vector.ext
    intro i hi
    rw [← extEq, ← prepared_chaining (compressionOf flags) (rightOf flags) (Fin.ofNat 10 r == 0) h e m]
    simp only [RV.blakeFinal, Vector.getElem_map, Vector.getElem_ofFn, Word.ofBitVec_roundtrip]
    have extWords : ∀ j (hj : j < 16), ext'[j].Bounded := by
      intro j hj
      simp only [ext', Vector.getElem_map]
      exact Word.ofBitVec_bound _
    apply BitVec.eq_of_toNat_eq
    have cb : ((Preparation.step ⟨Fin.ofNat 10 r == 0, compressionOf flags, rightOf flags, h, e, m⟩).chaining[i]).Bounded :=
      chainB ⟨i, hi⟩
    simp only [Fin.getElem_fin, Vector.getElem_map, BitVec.toNat_ofNat, BitVec.toNat_xor,
      Word.toBitVec_toNat cb,
      Word.toBitVec_toNat (extWords i (by omega)), Word.toBitVec_toNat (extWords (i + 8) (by omega)),
      show 8 + i = i + 8 by omega]
    apply Nat.mod_eq_of_lt
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Word.value_lt (chainB ⟨i, hi⟩))
      (Word.value_lt (extWords i (by omega)))) (Word.value_lt (extWords (i + 8) (by omega)))
  · simp only [last, decide_false, Bool.false_eq_true, ite_false]

end Airbender.Blake2Round.Proofs
