import Airbender.Review.Trace.Families.ReducedMachine.PC
import Airbender.Review.Circuits.ReducedMachine.Tables.Native

namespace Tests.NativeReducedPC
open Airbender Arithmetic Trace ReducedMachine Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- These assignments exercise only the eight exact imported increment
    assertions below. They are not full accepted 117-equation execution rows. -/
private def pcRow (low high carryLow carryHigh nextLow nextHigh : Nat)
    (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then low else if i = 1 then high else
  if i = 49 then nextLow else if i = 50 then nextHigh else
  if i = 51 then ((low : ZMod mersenne31Modulus) - 65532)⁻¹ else
  if i = 52 then carryLow else
  if i = 53 then ((carryLow : ZMod mersenne31Modulus) + high - 65536)⁻¹ else
  if i = 54 then carryHigh else 0

private def samples : Vector (Nat → ZMod mersenne31Modulus) 4 :=
  #v[pcRow 0 0 0 0 4 0,pcRow 65528 7 0 0 65532 7,
    pcRow 65532 65534 1 0 0 65535,pcRow 65532 65535 1 1 0 0]

private def assertionIndices : Vector (Fin 117) 8 :=
  #v[⟨18,by decide⟩,⟨19,by decide⟩,⟨34,by decide⟩,⟨35,by decide⟩,
    ⟨36,by decide⟩,⟨37,by decide⟩,⟨38,by decide⟩,⟨39,by decide⟩]

private def incrementAssertions (w : Nat → ZMod mersenne31Modulus) : Prop :=
  ∀ i : Fin 8, ((FlatOperation.constraints (importedConstraints NativeFixed.table)).get
    ⟨(assertionIndices[i]).val,by change (assertionIndices[i]).val < 117; exact (assertionIndices[i]).isLt⟩).eval
      (Verification.environment w) = 0

/-- Actual imported carry/inverse/select polynomials, at zero, the last
    noncarrying low word, low carry and complete RV32 wrap. -/
theorem actual_increment_edges (sample : Fin 4) : incrementAssertions samples[sample] := by
  intro i
  fin_cases sample <;> fin_cases i <;> decide +kernel

/-- Independent numerical fixture values retain the top-word rollover. -/
theorem edge_values :
    (⟨(samples[0] 49).val,(samples[0] 50).val⟩ : Word).toBitVec = 4 ∧
    (⟨(samples[1] 49).val,(samples[1] 50).val⟩ : Word).toBitVec = 0x7fffc ∧
    (⟨(samples[2] 49).val,(samples[2] 50).val⟩ : Word).toBitVec = 0xffff0000 ∧
    (⟨(samples[3] 0).val,(samples[3] 1).val⟩ : Word).toBitVec = 0xfffffffc ∧
    (⟨(samples[3] 49).val,(samples[3] 50).val⟩ : Word).toBitVec = 0 := by
  decide +kernel

theorem corrupt_low_rejected (sample : Fin 4) :
    ¬ incrementAssertions (fun i => if i = 49 then samples[sample] i + 1 else samples[sample] i) := by
  intro assertions
  have original := actual_increment_edges sample ⟨4,by decide⟩
  have bad := assertions ⟨4,by decide⟩
  simp [assertionIndices,importedConstraints,FlatOperation.constraints,
    Expression.eval,Verification.environment] at original bad
  have impossible : (-1 : ZMod mersenne31Modulus) = 0 := by linear_combination bad - original
  norm_num at impossible

theorem corrupt_high_rejected (sample : Fin 4) :
    ¬ incrementAssertions (fun i => if i = 50 then samples[sample] i + 1 else samples[sample] i) := by
  intro assertions
  have original := actual_increment_edges sample ⟨7,by decide⟩
  have bad := assertions ⟨7,by decide⟩
  simp [assertionIndices,importedConstraints,FlatOperation.constraints,
    Expression.eval,Verification.environment] at original bad
  have impossible : (-1 : ZMod mersenne31Modulus) = 0 := by linear_combination bad - original
  norm_num at impossible

/-- Full native acceptance plus the original query derives the wrap, with no
    assumed carry, output bound or expected output. -/
theorem decoded_wrap {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (top : entry.pc = 0xfffffffc) :
    (finalPCWord w).Bounded ∧ (finalPCWord w).toBitVec = 0 := by
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec entry.pc at canonical
  rw [top] at canonical
  have aligned : (initialPCWord w).lo % 4 = 0 := by rw [canonical]; decide +kernel
  have successor := NativePCProofs.selected_pc_successor native fields query aligned
  rw [canonical] at successor
  simpa only [Word.ofBitVec_roundtrip,show (0xfffffffc : BitVec 32) + 4 = 0 from by decide +kernel] using successor

theorem oversized_successor_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (decoded : ShiftDecodedTrace trace setup) (row : Row mersenne31Modulus NativeReducedFamily)
    (present : row ∈ trace.rows) (large : limbBase ≤ (finalPCWord row.assignment).lo) :
    ¬ Accepted trace := by
  intro accepted
  have bounds := (public_shift_pc_successor image accepted decoded row present).2.2.1
  exact Nat.not_le_of_gt bounds.1 large

/-- The native successor matches the exact original decoded public PC. -/
theorem original_query_successor {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (aligned : (initialPCWord w).lo % 4 = 0) :
    (finalPCWord w).toBitVec = entry.pc + 4 := by
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec entry.pc at canonical
  simpa only [canonical,Word.ofBitVec_roundtrip] using
    (NativePCProofs.selected_pc_successor native fields query aligned).2

/-- Discarded GPR writes do not discard native PC advancement. -/
theorem discarded_pc_advances {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (aligned : (initialPCWord w).lo % 4 = 0)
    (discarded : entry.data.rd = 0) :
    rdZeroFlag w = 1 ∧ (finalPCWord w).toBitVec ≠ (initialPCWord w).toBitVec := by
  constructor
  · simpa [discarded] using (NativeShiftDecoderProofs.decoded_fields fields query).zero
  · intro same
    have successor := (NativePCProofs.selected_pc_successor native fields query aligned).2
    have no_fixed (pc : BitVec 32) : pc + 4 ≠ pc := by
      intro fixed
      have bad := congrArg BitVec.toNat fixed
      change (pc.toNat + 4) % 4294967296 = pc.toNat at bad
      have small := pc.isLt
      change pc.toNat < 4294967296 at small
      omega
    exact no_fixed _ (successor.symm.trans same)

end Tests.NativeReducedPC
