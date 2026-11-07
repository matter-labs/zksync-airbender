import Airbender.Proofs.Keccak.SplitNativeCallExecution

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
private theorem code_word_bound {code low high : Nat} (equation : code = Nat.pair low high)
    (lower : low < 65536) (upper : high < 65536) :
    (Word.mk (Nat.unpair code).1 (Nat.unpair code).2).Bounded := by
  rw [equation, Nat.unpair_pair]
  exact ⟨lower, upper⟩

variable [Fact babyBearModulus.Prime]

/-- All actual parity write tokens retain canonical raw native word limbs. -/
theorem parity_write_words_bounded (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable else ColumnParity.clockConstraints columnParityFixedTable))
    (active : w 0 = 1)
    (boundedReads : ∀ port ∈ (⟨.columnParity, w⟩ : Row babyBearModulus).ports cached,
      (readToken w port).word.Bounded) :
    ∀ port ∈ (⟨.columnParity, w⟩ : Row babyBearModulus).ports cached,
      ((⟨.columnParity, w⟩ : Row babyBearModulus).writeToken cached port).word.Bounded := by
  obtain ⟨index, _, _, next, selected⟩ := parity_native_controller_schedule cached w holds active
  have control :
      ((⟨.columnParity, w⟩ : Row babyBearModulus).writeToken cached (parityControlPort cached)).word.Bounded := by
    change (Word.mk (Nat.unpair ((parityControlPort cached).writeCode w)).1
      (Nat.unpair ((parityControlPort cached).writeCode w)).2).Bounded
    apply code_word_bound
    · exact (parity_control_port_codes cached w holds).2
    · rw [next, ZMod.val_natCast_of_lt
        (lt_trans (split_control_limb_bounds index).2 (by decide : 65536 < babyBearModulus))]
      exact (split_control_limb_bounds index).2
    · decide
  have pointer :
      ((⟨.columnParity, w⟩ : Row babyBearModulus).writeToken cached (parityPointerPort cached)).word.Bounded := by
    change (Word.mk (Nat.unpair ((parityPointerPort cached).writeCode w)).1
      (Nat.unpair ((parityPointerPort cached).writeCode w)).2).Bounded
    rw [(parity_pointer_port cached w).2.2]
    exact boundedReads _ (parity_call_ports_present cached w).2.1
  have laneBound (lane : Fin 6) (limb : Fin 4) :
      (parityLaneLimb cached true w lane limb).val < 65536 := by
    exact (parity_write_limb_value cached w holds lane limb).1
  have lanes (lane : Fin 6) (high : Bool) :
      ((⟨.columnParity, w⟩ : Row babyBearModulus).writeToken cached (parityLanePort cached lane high)).word.Bounded := by
    change (Word.mk (Nat.unpair ((parityLanePort cached lane high).writeCode w)).1
      (Nat.unpair ((parityLanePort cached lane high).writeCode w)).2).Bounded
    apply code_word_bound (parity_lane_port_values cached true high w lane)
    · exact laneBound lane _
    · exact laneBound lane _
  intro port member
  simp only [← Array.mem_toList_iff, parity_ports_enumeration] at member
  rcases List.mem_append.mp member with register | memory
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at register
    rcases register with rfl | rfl
    · exact control
    · exact pointer
  · obtain ⟨lane, _, present⟩ := List.mem_flatMap.mp memory
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact lanes lane false
    · exact lanes lane true

/-- All actual theta write tokens retain canonical raw native word limbs. -/
theorem theta_write_words_bounded (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable else ThetaRho.clockConstraints thetaRhoFixedTable))
    (active : w 0 = 1)
    (boundedReads : ∀ port ∈ (⟨.thetaRho, w⟩ : Row babyBearModulus).ports cached,
      (readToken w port).word.Bounded) :
    ∀ port ∈ (⟨.thetaRho, w⟩ : Row babyBearModulus).ports cached,
      ((⟨.thetaRho, w⟩ : Row babyBearModulus).writeToken cached port).word.Bounded := by
  obtain ⟨index, _, _, next, selected⟩ := theta_native_controller_schedule cached w holds active
  have control :
      ((⟨.thetaRho, w⟩ : Row babyBearModulus).writeToken cached (thetaControlPort cached)).word.Bounded := by
    change (Word.mk (Nat.unpair ((thetaControlPort cached).writeCode w)).1
      (Nat.unpair ((thetaControlPort cached).writeCode w)).2).Bounded
    apply code_word_bound
    · exact (theta_control_port_codes cached w holds).2
    · rw [next, ZMod.val_natCast_of_lt
        (lt_trans (split_control_limb_bounds index).2 (by decide : 65536 < babyBearModulus))]
      exact (split_control_limb_bounds index).2
    · decide
  have pointer :
      ((⟨.thetaRho, w⟩ : Row babyBearModulus).writeToken cached (thetaPointerPort cached)).word.Bounded := by
    change (Word.mk (Nat.unpair ((thetaPointerPort cached).writeCode w)).1
      (Nat.unpair ((thetaPointerPort cached).writeCode w)).2).Bounded
    rw [(theta_pointer_port cached w).2.2]
    exact boundedReads _ (theta_call_ports_present cached w).2.1
  have laneBound (lane : Fin 7) (limb : Fin 4) :
      (thetaLaneLimb cached true w lane limb).val < 65536 := by
    apply theta_all_write_limb_bounds cached w holds
      ⟨index.val % 5, Nat.mod_lt _ (by decide)⟩ selected
    intro source high
    exact boundedReads _ ((theta_call_ports_present cached w).2.2 source high)
  have lanes (lane : Fin 7) (high : Bool) :
      ((⟨.thetaRho, w⟩ : Row babyBearModulus).writeToken cached (thetaLanePort cached lane high)).word.Bounded := by
    change (Word.mk (Nat.unpair ((thetaLanePort cached lane high).writeCode w)).1
      (Nat.unpair ((thetaLanePort cached lane high).writeCode w)).2).Bounded
    apply code_word_bound (theta_lane_port_values cached true high w lane)
    · exact laneBound lane _
    · exact laneBound lane _
  intro port member
  simp only [← Array.mem_toList_iff, theta_ports_enumeration] at member
  rcases List.mem_append.mp member with register | memory
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at register
    rcases register with rfl | rfl
    · exact control
    · exact pointer
  · obtain ⟨lane, _, present⟩ := List.mem_flatMap.mp memory
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact lanes lane false
    · exact lanes lane true

/-- All actual chi5 write tokens retain canonical raw native word limbs. -/
theorem chi5_write_words_bounded (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (active : w 0 = 1)
    (boundedReads : ∀ port ∈ (⟨.chi5, w⟩ : Row babyBearModulus).ports cached,
      (readToken w port).word.Bounded) :
    ∀ port ∈ (⟨.chi5, w⟩ : Row babyBearModulus).ports cached,
      ((⟨.chi5, w⟩ : Row babyBearModulus).writeToken cached port).word.Bounded := by
  obtain ⟨index, _, _, next, selected⟩ := chi5_native_controller_schedule cached w holds active
  have control :
      ((⟨.chi5, w⟩ : Row babyBearModulus).writeToken cached (chi5ControlPort cached)).word.Bounded := by
    change (Word.mk (Nat.unpair ((chi5ControlPort cached).writeCode w)).1
      (Nat.unpair ((chi5ControlPort cached).writeCode w)).2).Bounded
    apply code_word_bound
    · exact (chi5_control_port_codes cached w holds).2
    · rw [next, ZMod.val_natCast_of_lt
        (lt_trans (split_control_limb_bounds index).2 (by decide : 65536 < babyBearModulus))]
      exact (split_control_limb_bounds index).2
    · decide
  have pointer :
      ((⟨.chi5, w⟩ : Row babyBearModulus).writeToken cached (chi5PointerPort cached)).word.Bounded := by
    change (Word.mk (Nat.unpair ((chi5PointerPort cached).writeCode w)).1
      (Nat.unpair ((chi5PointerPort cached).writeCode w)).2).Bounded
    rw [(chi5_pointer_port cached w).2.2]
    exact boundedReads _ (chi5_call_ports_present cached w).2.1
  have laneBound (lane : Fin 5) (limb : Fin 4) :
      (chi5LaneLimb cached true w lane limb).val < 65536 := by
    exact (chi5_lane_limb_value cached true w holds lane limb).1
  have lanes (lane : Fin 5) (high : Bool) :
      ((⟨.chi5, w⟩ : Row babyBearModulus).writeToken cached (chi5LanePort cached lane high)).word.Bounded := by
    change (Word.mk (Nat.unpair ((chi5LanePort cached lane high).writeCode w)).1
      (Nat.unpair ((chi5LanePort cached lane high).writeCode w)).2).Bounded
    apply code_word_bound (chi5_lane_port_values cached true high w lane)
    · exact laneBound lane _
    · exact laneBound lane _
  intro port member
  simp only [← Array.mem_toList_iff, chi5_ports_enumeration] at member
  rcases List.mem_append.mp member with register | memory
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at register
    rcases register with rfl | rfl
    · exact control
    · exact pointer
  · obtain ⟨lane, _, present⟩ := List.mem_flatMap.mp memory
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact lanes lane false
    · exact lanes lane true

/-- Native split equations propagate initialized raw read-word bounds to every actual write word. -/
theorem native_write_words_bounded (cached : Bool) (row : Row babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints cached fixedSetup))
    (active : row.assignment (row.columns cached).execute = 1)
    (boundedReads : ∀ port ∈ row.ports cached, (readToken row.assignment port).word.Bounded) :
    ∀ port ∈ row.ports cached, (row.writeToken cached port).word.Bounded := by
  rcases row with ⟨kind, w⟩
  have executing : w 0 = 1 := by cases kind <;> cases cached <;> exact active
  cases kind with
  | columnParity =>
    apply parity_write_words_bounded cached w _ executing boundedReads
    cases cached <;> exact holds
  | thetaRho =>
    apply theta_write_words_bounded cached w _ executing boundedReads
    cases cached <;> exact holds
  | chi5 =>
    apply chi5_write_words_bounded cached w _ executing boundedReads
    cases cached <;> exact holds

end Airbender.Keccak.Split.Native.Proofs
