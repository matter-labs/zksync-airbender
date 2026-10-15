import Airbender.Proofs.UnifiedReduced.Decoder
import Airbender.Proofs.UnifiedReduced.Trace
import Airbender.Proofs.Trace.ZeroRegister
import Airbender.Proofs.Trace.RowHistory

namespace Airbender.UnifiedReduced.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

private theorem jump_zero_marker {instruction : SailRV32.instruction}
    {data : DecoderData Unit} (fields : JumpBranchSlt.decoderFields instruction = some data)
    (zero : data.rd = 0) : (jumpFields data).mask.testBit 14 = true ∧
      ∃ i : Fin 4, (jumpFields data).mask.testBit (10 + i.val) = true := by
  unfold JumpBranchSlt.decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (simp only [Option.some.injEq] at fields; subst data
       simp_all [jumpFields, DecoderData.mapFamily])
    | (cases fields)
  all_goals decide

private theorem binary_nonzero {instruction : SailRV32.instruction}
    {data : DecoderData Unit} (fields : ShiftBinop.decoderFields instruction = some data) : data.rd ≠ 0 := by
  unfold ShiftBinop.decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (unfold ShiftBinop.instructionFields at fields
       split at fields
       · cases fields
       · simp only [Option.some.injEq] at fields; subst data; assumption)
    | cases fields

private theorem word_mask {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : Trace.decoderFields instruction = some data) (family : data.family = .wordMemory) :
    data.mask = 0 ∨ data.mask = 1 := by
  unfold Trace.decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (simp only [Option.some.injEq] at fields; subst data
       simp_all [Trace.arithmeticFields])
    | cases fields
  all_goals split_ifs at family ⊢

theorem decoder_zero_cases {instruction : SailRV32.instruction} {data : DecoderData UnifiedFamily}
    (fields : decoderFields instruction = some data) (zero : data.rd = 0) :
    data = ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ ∨
      (data.mask.testBit 14 = true ∧ ∃ i : Fin 4, data.mask.testBit (10 + i.val) = true) ∨
      data.mask.testBit 18 = true := by
  unfold decoderFields at fields
  cases first : Trace.decoderFields instruction with
  | some original =>
    simp [first] at fields
    subst data
    change original.rd = 0 at zero
    cases family : original.family
    · have nop := Trace.Proofs.decoder_zero_nop first family zero
      subst original
      exact Or.inl rfl
    · rcases word_mask first family with load | store
      · exact False.elim (Trace.Proofs.decoder_load_nonzero first family load zero)
      · right; right
        simp [arithmeticFields, DecoderData.mapFamily, family, store]
        decide
  | none =>
    cases second : JumpBranchSlt.decoderFields instruction with
    | some original =>
      simp [first, second] at fields
      subst data
      exact Or.inr (Or.inl (jump_zero_marker second zero))
    | none =>
      cases third : ShiftBinop.decoderFields instruction with
      | none => simp [first, second, third] at fields
      | some original =>
        simp [first, second, third] at fields
        subst data
        exact False.elim (binary_nonzero third zero)

theorem zero_operands_result [Fact p.Prime] (hp : 196608 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) (selected : w 11 = 1)
    (operands : w 36 = 0 ∧ w 37 = 0 ∧ w 42 = 0 ∧ w 43 = 0 ∧ w 8 = 0 ∧ w 9 = 0) :
    (⟨(w 50).val, (w 51).val⟩ : Word).toBitVec = 0 := by
  have other := dispatch_exclusive (by omega) h active 0 selected
  have flags : w 12 = 0 ∧ w 13 = 0 ∧ w 14 = 0 ∧ w 15 = 0 ∧
      w 16 = 0 ∧ w 17 = 0 ∧ w 20 = 0 := by
    repeat' apply And.intro
    all_goals first
      | exact other 1 (by decide) | exact other 2 (by decide)
      | exact other 3 (by decide) | exact other 4 (by decide)
      | exact other 5 (by decide) | exact other 6 (by decide)
      | exact other 9 (by decide)
  have low := Verification.assertion_of_holds h ⟨4, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected, flags.1, flags.2.1, flags.2.2.1, flags.2.2.2.1, flags.2.2.2.2.1,
    flags.2.2.2.2.2.1, flags.2.2.2.2.2.2, operands.1, operands.2.1,
    operands.2.2.1, operands.2.2.2.1, operands.2.2.2.2.1, operands.2.2.2.2.2] at low high
  have carry := boolean_val (local_flags h 21)
  have overflow := boolean_val (local_flags h 20)
  change (w 53).val ≤ 1 at carry
  change (w 52).val ≤ 1 at overflow
  have loEq : (0 : ZMod p) + 0 + 0 = (w 50).val + 65536 * (w 53).val := by
    simp only [ZMod.natCast_zmod_val]
    apply sub_eq_zero.mp
    linear_combination low
  have hiEq : ((w 53).val : ZMod p) + 0 + 0 + 0 = (w 51).val + 65536 * (w 52).val := by
    simp only [ZMod.natCast_zmod_val]
    apply sub_eq_zero.mp
    linear_combination high
  have zeroBound : (⟨0, 0⟩ : Word).Bounded := ⟨by decide, by decide⟩
  simpa [Word.toBitVec, Word.value] using Word.add_of_limbs
    (left := ⟨0, 0⟩) (right := ⟨0, 0⟩) (immediate := ⟨0, 0⟩)
    (output := ⟨(w 50).val, (w 51).val⟩) hp zeroBound zeroBound zeroBound
    (destination_bounds h) (Nat.le_trans carry (by decide)) (Nat.le_trans overflow (by decide))
    (by simpa only [Nat.cast_zero] using loEq) (by simpa only [Nat.cast_zero] using hiEq)

theorem row_zero_preserving_of_metadata [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) {entry : ProgramEntry} (query : decoderQuery w = entry.query)
    (flags : ∀ i : Fin 19, w importedConstraintsDecoderColumns.flags[i] =
      if entry.data.mask.testBit i.val then 1 else 0)
    (zeroCases : entry.data.rd = 0 →
      entry.data = ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ ∨
        (entry.data.mask.testBit 14 = true ∧ ∃ i : Fin 4, entry.data.mask.testBit (10 + i.val) = true) ∨
        entry.data.mask.testBit 18 = true) :
    Trace.Proofs.RowZeroPreserving (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) := by
  intro port present zero reads
  simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact reads _ (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]) le_rfl zero
  · exact reads _ (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]) le_rfl zero
  · have address : (w 29).val = 0 ∧ (w 44).val = 0 ∧ (w 45).val = 0 := by
      simpa [MemoryAddress.code, pairCode, Cell.addressCode, Nat.pair_eq_pair] using zero
    have noRAM : w 29 = 0 := by simpa using address.1
    have location := Verification.assertion_of_holds h ⟨31, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, noRAM] at location
    have targetZero : w 7 = 0 := by
      have lo : w 44 = 0 := by simpa using address.2.1
      rw [lo] at location
      linear_combination -location
    have rd := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query
    change w 7 = (entry.data.rd.toNat : ZMod p) at rd
    have originalZero : entry.data.rd = 0 := by
      have value := congrArg ZMod.val rd
      rw [targetZero, ZMod.val_zero, ZMod.val_natCast_of_lt (by have := entry.data.rd.isLt; omega)] at value
      exact BitVec.eq_of_toNat_eq value.symm
    rcases zeroCases originalZero with nop | ⟨marker, i, operation⟩ | store
    · rw [nop] at flags
      have rs1 := congrArg (fun q : Vector (ZMod p) 9 => q[2]) query
      have rs2 := congrArg (fun q : Vector (ZMod p) 9 => q[3]) query
      have immLo := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
      have immHi := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
      change w 5 = (entry.data.rs1.toNat : ZMod p) at rs1
      change w 6 = (entry.data.rs2.toNat : ZMod p) at rs2
      change w 8 = (entry.data.immediate.lo : ZMod p) at immLo
      change w 9 = (entry.data.immediate.hi : ZMod p) at immHi
      rw [nop] at rs1 rs2 immLo immHi
      norm_num at rs1 rs2 immLo immHi
      have selected : w 11 = 1 := by simpa [importedConstraintsDecoderColumns] using flags 0
      have noReadRAM : w 28 = 0 := by simpa [importedConstraintsDecoderColumns] using (show w importedConstraintsDecoderColumns.flags[17] = 0 from flags 17)
      have low := Verification.assertion_of_holds h ⟨29, by rw [constraint_count]; decide⟩
      have high := Verification.assertion_of_holds h ⟨30, by rw [constraint_count]; decide⟩
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, noReadRAM, rs2] at low high
      have secondLo : w 38 = 0 := by linear_combination low
      have secondHi : w 39 = 0 := by linear_combination high
      have left := reads importedConstraintsMemoryPorts[0]
        (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
        (by change (decodeTimestamp w _).value + 0 ≤ (decodeTimestamp w _).value + 2; omega)
        (by simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, rs1])
      have right := reads importedConstraintsMemoryPorts[1]
        (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
        (by change (decodeTimestamp w _).value + 1 ≤ (decodeTimestamp w _).value + 2; omega)
        (by simp [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
          Cell.addressCode, noReadRAM, secondLo, secondHi])
      have leftLimbs : w 36 = 0 ∧ w 37 = 0 := by
        change Nat.pair (w 36).val (w 37).val = Nat.pair 0 0 at left
        simpa using Nat.pair_eq_pair.mp left
      have rightLimbs : w 42 = 0 ∧ w 43 = 0 := by
        change Nat.pair (w 42).val (w 43).val = Nat.pair 0 0 at right
        simpa using Nat.pair_eq_pair.mp right
      have result := zero_operands_result (by omega) h active selected
        ⟨leftLimbs.1, leftLimbs.2, rightLimbs.1, rightLimbs.2, immLo, immHi⟩
      have value := congrArg BitVec.toNat result
      rw [Word.toBitVec_toNat (destination_bounds h)] at value
      have limbs : (w 50).val = 0 ∧ (w 51).val = 0 := by
        change (w 50).val + limbBase * (w 51).val = 0 at value
        dsimp [limbBase] at value
        omega
      simp [writeToken, MemoryPort.writeCode, pairCode, limbs.1, limbs.2]
      rfl
    · have selected : w Variables.dispatchColumns[10 + i.val] = 1 := by
        have bit := flags ⟨10 + i.val, by have := i.isLt; omega⟩
        rw [operation] at bit
        fin_cases i <;> simpa [Variables.dispatchColumns, importedConstraintsDecoderColumns] using bit
      have other := dispatch_exclusive (by omega) h active ⟨10 + i.val, by have := i.isLt; omega⟩ selected
      have marked : w 25 = 1 := by simpa [marker, importedConstraintsDecoderColumns] using flags 14
      have gate := Verification.assertion_of_holds h ⟨21, by rw [constraint_count]; decide⟩
      have low := Verification.assertion_of_holds h ⟨25, by rw [constraint_count]; decide⟩
      have high := Verification.assertion_of_holds h ⟨26, by rw [constraint_count]; decide⟩
      have familySum : w 21 + w 22 + w 23 + w 24 = 1 := by
        fin_cases i
        · have one : w 21 = 1 := by simpa [Variables.dispatchColumns] using selected
          have zero1 : w 22 = 0 := by
            simpa [Variables.dispatchColumns] using other 11 (by norm_num [Fin.ext_iff])
          have zero2 : w 23 = 0 := by
            simpa [Variables.dispatchColumns] using other 12 (by norm_num [Fin.ext_iff])
          have zero3 : w 24 = 0 := by
            simpa [Variables.dispatchColumns] using other 13 (by norm_num [Fin.ext_iff])
          simp [one, zero1, zero2, zero3]
        · have one : w 22 = 1 := by simpa [Variables.dispatchColumns] using selected
          have zero0 : w 21 = 0 := by
            simpa [Variables.dispatchColumns] using other 10 (by norm_num [Fin.ext_iff])
          have zero2 : w 23 = 0 := by
            simpa [Variables.dispatchColumns] using other 12 (by norm_num [Fin.ext_iff])
          have zero3 : w 24 = 0 := by
            simpa [Variables.dispatchColumns] using other 13 (by norm_num [Fin.ext_iff])
          simp [one, zero0, zero2, zero3]
        · have one : w 23 = 1 := by simpa [Variables.dispatchColumns] using selected
          have zero0 : w 21 = 0 := by
            simpa [Variables.dispatchColumns] using other 10 (by norm_num [Fin.ext_iff])
          have zero1 : w 22 = 0 := by
            simpa [Variables.dispatchColumns] using other 11 (by norm_num [Fin.ext_iff])
          have zero3 : w 24 = 0 := by
            simpa [Variables.dispatchColumns] using other 13 (by norm_num [Fin.ext_iff])
          simp [one, zero0, zero1, zero3]
        · have one : w 24 = 1 := by simpa [Variables.dispatchColumns] using selected
          have zero0 : w 21 = 0 := by
            simpa [Variables.dispatchColumns] using other 10 (by norm_num [Fin.ext_iff])
          have zero1 : w 22 = 0 := by
            simpa [Variables.dispatchColumns] using other 11 (by norm_num [Fin.ext_iff])
          have zero2 : w 23 = 0 := by
            simpa [Variables.dispatchColumns] using other 12 (by norm_num [Fin.ext_iff])
          simp [one, zero0, zero1, zero2]
      have enabled : w 85 = 1 := by
        simp [importedConstraints, FlatOperation.constraints, Expression.eval,
          Verification.environment, marked] at gate
        linear_combination gate + familySum
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, enabled] at low high
      simp [writeToken, MemoryPort.writeCode, pairCode, low, high]
      rfl
    · have ram : w 29 = 1 := by simpa [store, importedConstraintsDecoderColumns] using flags 18
      exact False.elim (zero_ne_one (noRAM.symm.trans ram))

theorem row_zero_preserving [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) {before : Reference.RiscV.Sail.State} (fetch : Fetched w before) :
    Trace.Proofs.RowZeroPreserving (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) := by
  obtain ⟨entry, source, query, flags⟩ := fetch
  exact row_zero_preserving_of_metadata hp h active query flags (decoder_zero_cases source.fields)

end Airbender.UnifiedReduced.Proofs
