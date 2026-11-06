import Airbender.Proofs.ReducedMachine.NativeShiftWrite
import Airbender.Proofs.ReducedMachine.NativeShiftDecoder
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Sail.PC
import Airbender.Review.Circuits.ReducedMachine.PC

namespace Airbender.ReducedMachine.NativePCProofs
open Native Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The unchanged native increment gadget uses Boolean carry columns 52/54,
    inverse columns 51/53 and actual default candidate columns 49/50. Its output
    bounds are derived from its gates, inverses and the decoded incoming PC. -/
theorem default_pc_successor {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {initial final : Word} {w : Nat → ZMod p}
    {setup : Table (ZMod p) (fields 4)}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mapping : w 0 = (initial.lo : ZMod p) ∧ w 1 = (initial.hi : ZMod p) ∧
      final.lo = (w 49).val ∧ final.hi = (w 50).val)
    (bounds : initial.Bounded) (aligned : initial.lo % 4 = 0) :
    final.Bounded ∧ final.toBitVec = initial.toBitVec + 4 := by
  have bitLo := Verification.assertion_of_holds h ⟨18, by change 18 < 117; decide⟩
  have bitHi := Verification.assertion_of_holds h ⟨19, by change 19 < 117; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at bitLo bitHi
  obtain ⟨c, cb, hc⟩ := Arithmetic.boolean_nat (by convert bitLo using 1; ring)
  obtain ⟨d, db, hd⟩ := Arithmetic.boolean_nat (by convert bitHi using 1; ring)
  have outLo : w 49 = (final.lo : ZMod p) := by
    rw [mapping.2.2.1]; exact (ZMod.natCast_zmod_val _).symm
  have outHi : w 50 = (final.hi : ZMod p) := by
    rw [mapping.2.2.2]; exact (ZMod.natCast_zmod_val _).symm
  have gateLo := Verification.assertion_of_holds h ⟨34, by change 34 < 117; decide⟩
  have invLo := Verification.assertion_of_holds h ⟨35, by change 35 < 117; decide⟩
  have writeLo := Verification.assertion_of_holds h ⟨36, by change 36 < 117; decide⟩
  have gateHi := Verification.assertion_of_holds h ⟨37, by change 37 < 117; decide⟩
  have invHi := Verification.assertion_of_holds h ⟨38, by change 38 < 117; decide⟩
  have writeHi := Verification.assertion_of_holds h ⟨39, by change 39 < 117; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    hc, hd, mapping.1, mapping.2.1, outLo, outHi] at gateLo invLo writeLo gateHi invHi writeHi
  have low : (initial.lo : ZMod p) + 4 = final.lo + 65536 * c := by
    linear_combination gateLo + writeLo
  have high : (c : ZMod p) + initial.hi = final.hi + 65536 * d := by
    linear_combination gateHi + writeHi
  have il := bounds.1; have ih := bounds.2
  unfold limbBase at il ih
  have lowBound : final.lo < 65536 := by
    interval_cases c
    · have different : initial.lo ≠ 65532 := by
        intro same
        rw [same] at invLo
        have bad : (-1 : ZMod p) = 0 := by linear_combination invLo
        norm_num at bad
      have small : initial.lo + 4 < 65536 := by omega
      have eq : (final.lo : ZMod p) = ((initial.lo + 4 : Nat) : ZMod p) := by
        push_cast; simpa using low.symm
      have valEq := congrArg ZMod.val eq
      have op : final.lo < p := by rw [mapping.2.2.1]; exact ZMod.val_lt _
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt op,
        Nat.mod_eq_of_lt (show initial.lo + 4 < p by omega)] at valEq
      omega
    · have same : initial.lo = 65532 := by
        apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega)
        linear_combination gateLo
      have zero : (final.lo : ZMod p) = 0 := by
        rw [same] at low; linear_combination -low
      have op : final.lo < p := by rw [mapping.2.2.1]; exact ZMod.val_lt _
      have valEq := congrArg ZMod.val zero
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt op, ZMod.val_zero] at valEq
      omega
  have highBound : final.hi < 65536 := by
    interval_cases d
    · have different : c + initial.hi ≠ 65536 := by
        intro same
        have eq : (c : ZMod p) + initial.hi = 65536 := by
          simpa only [Nat.cast_add, Nat.cast_ofNat] using congrArg (fun n : Nat => (n : ZMod p)) same
        have bad : w 53 * ((c : ZMod p) + initial.hi - 65536) - 1 = 0 := by
          convert invHi using 1; ring
        simp [eq] at bad
      have small : c + initial.hi < 65536 := by omega
      have eq : (final.hi : ZMod p) = ((c + initial.hi : Nat) : ZMod p) := by
        push_cast; simpa using high.symm
      have op : final.hi < p := by rw [mapping.2.2.2]; exact ZMod.val_lt _
      have valEq := congrArg ZMod.val eq
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt op,
        Nat.mod_eq_of_lt (show c + initial.hi < p by omega)] at valEq
      omega
    · have same : c + initial.hi = 65536 := by
        apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega)
        push_cast; linear_combination gateHi
      have zero : (final.hi : ZMod p) = 0 := by
        have eq : (c : ZMod p) + initial.hi = 65536 := by
          simpa only [Nat.cast_add, Nat.cast_ofNat] using congrArg (fun n : Nat => (n : ZMod p)) same
        linear_combination eq - high
      have op : final.hi < p := by rw [mapping.2.2.2]; exact ZMod.val_lt _
      have valEq := congrArg ZMod.val zero
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt op, ZMod.val_zero] at valEq
      omega
  have finalBounds : final.Bounded := ⟨lowBound, highBound⟩
  refine ⟨finalBounds, ?_⟩
  simpa [Word.toBitVec, Word.value] using Word.add_of_limbs hp bounds
    (right := ⟨0, 0⟩) (immediate := ⟨4, 0⟩) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    finalBounds (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide))
    (by simpa using low) (by simpa using high)

/-- The original public query fixes the canonical incoming RV32 PC. -/
theorem query_pc_bound {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry}
    (query : decoderQuery w = entry.query) : (initialPCWord w).Bounded := by
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec entry.pc at canonical
  rw [canonical]
  exact Word.ofBitVec_bound _

/-- The recovered original instruction selects the default candidate. Both its
    bounds and complete RV32 successor are proved, with top-word rollover. -/
theorem selected_pc_successor {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (aligned : (initialPCWord w).lo % 4 = 0) :
    (finalPCWord w).Bounded ∧ (finalPCWord w).toBitVec = (initialPCWord w).toBitVec + 4 := by
  obtain ⟨_,useRegister,mask,_⟩ := NativeShiftDecoderProofs.field_bounds fields
  have selected : w 12 = (entry.data.family.mask useRegister : ZMod mersenne31Modulus) := by
    have same := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
    change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at same
    simpa only [mask] using same
  have pc := NativeShiftWriteProofs.pc native entry.data.family useRegister selected
  unfold finalPC at pc
  rw [NativePortProofs.final_pc_columns] at pc
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) pc
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) pc
  simp [defaultPC] at low high
  apply default_pc_successor (by decide : 196608 < mersenne31Modulus) native
    (initial := initialPCWord w) (final := finalPCWord w)
    ⟨(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm,
      congrArg ZMod.val low,congrArg ZMod.val high⟩ (query_pc_bound query) aligned

/-- Full original public decoding derives the incoming PC range and alignment;
    no local range, exclusion, output or successor answer is supplied. -/
theorem decoded_pc_successor {w : Nat → ZMod mersenne31Modulus}
    {setup : Trace.SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat} {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (member : setup.table.Contains #[] (decoderQuery w)) : ShiftPCSuccessor w := by
  obtain ⟨entry,present,source,query⟩ := NativeShiftDecoderProofs.fetched_sources image native member
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec entry.pc at canonical
  have aligned : (initialPCWord w).lo % 4 = 0 := by
    rw [canonical]
    exact (Trace.Proofs.run_sparse_setup_sources image present).2
  exact ⟨query_pc_bound query,aligned,selected_pc_successor native source.fields query aligned⟩

end Airbender.ReducedMachine.NativePCProofs
