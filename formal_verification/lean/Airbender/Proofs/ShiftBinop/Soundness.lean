import Airbender.Proofs.ShiftBinop.RowModel
import Airbender.Proofs.ShiftBinop
import Airbender.Proofs.ShiftBinop.Shifts
import Airbender.Proofs.ByteTables
import Airbender.Proofs.Arithmetic.Bytes
import Airbender.Proofs.Sail.PC

namespace Airbender.ShiftBinop.Proofs
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

private theorem wiring {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 1) :
    ∀ i : Fin 4,
      w (56 + 9 * i.val) = w (19 + i.val) ∧
      w (57 + 9 * i.val) = w (25 + i.val) +
        (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35) ∧
      w (58 + 9 * i.val) = w (36 + i.val) ∧
      w (64 + 9 * i.val) = w 10 := by
  intro i
  have a := Verification.assertion_of_holds h
    ⟨5 + 9 * i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have b := Verification.assertion_of_holds h
    ⟨6 + 9 * i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have c := Verification.assertion_of_holds h
    ⟨7 + 9 * i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have t := Verification.assertion_of_holds h
    ⟨13 + 9 * i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  fin_cases i <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected.1, selected.2] at a b c t ⊢
  all_goals
    repeat' apply And.intro
    all_goals solve | linear_combination a | linear_combination b |
      linear_combination c | linear_combination t

/-- The imported byte query enforces both source bounds and the output byte.
    Shared by the local ISA proof and native port interpretation. -/
theorem binary_query_values {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 1) (tag : Nat)
    (validTag : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (tag : ZMod p))
    (i : Fin 4) : (w (19 + i.val)).val < 256 ∧
      (w (25 + i.val) + (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35)).val < 256 ∧
      (w (36 + i.val)).val < 256 ∧ BitVec.ofNat 8 (w (36 + i.val)).val =
        Verification.byteOperation tag (BitVec.ofNat 8 (w (19 + i.val)).val)
          (BitVec.ofNat 8 (w (25 + i.val) +
            (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35)).val) := by
  have wires := wiring h selected i
  have query := Verification.lookup_of_holds h
    ⟨3 + i.val, by rw [lookup_count]; have := i.isLt; omega⟩
  fin_cases i
  all_goals
    norm_num only at wires
    have value := Verification.binary_lookup hp query tag validTag
      (by simpa [Expression.eval, Verification.environment, wires.2.2.2] using funct3)
    simpa [Expression.eval, Verification.environment, wires.1, wires.2.1,
      wires.2.2.1] using value

private theorem byte_result {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {input : Input} {output : Sail.Output} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (interface : RowInterfaces input output w)
    (mapping : RowWordMapping input output w)
    (binary : input.operation.isShift = false) :
    ∀ i : Fin 4, (w (36 + i.val)).val =
      ((Verification.byteOperation input.operation.tag input.left input.right).extractLsb'
        (8 * i.val) 8).toNat := by
  intro i
  have selected : w 11 = 0 ∧ w 12 = 1 := by simpa [binary] using interface.selected
  have validTag : input.operation.tag = 4 ∨ input.operation.tag = 6 ∨ input.operation.tag = 7 := by
    cases op : input.operation <;> simp_all [Operation.tag, Operation.isShift]
  have values := binary_query_values hp h selected input.operation.tag validTag interface.funct3 i
  have left := mapping.leftBytes i
  have right := mapping.binaryRightBytes binary i
  rw [left, right] at values
  have lb := (input.left.extractLsb' (8 * i.val) 8).isLt
  have rb := (input.right.extractLsb' (8 * i.val) 8).isLt
  have lc : ((input.left.extractLsb' (8 * i.val) 8).toNat : ZMod p).val =
      (input.left.extractLsb' (8 * i.val) 8).toNat := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have rc : ((input.right.extractLsb' (8 * i.val) 8).toNat : ZMod p).val =
      (input.right.extractLsb' (8 * i.val) 8).toNat := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [lc, rc] at values
  have eq := congrArg BitVec.toNat values.2.2.2
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt values.2.2.1,
    BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq] at eq
  rw [eq]
  cases op : input.operation <;>
    simp_all [Operation.isShift, Verification.byteOperation, Operation.tag, BitVec.extractLsb'_xor,
      BitVec.extractLsb'_or, BitVec.extractLsb'_and]

private theorem destination {p : Nat} [Fact p.Prime] (hp : 65536 < p)
    {input : Input} {output : Sail.Output} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (interface : RowInterfaces input output w)
    (mapping : RowWordMapping input output w)
    (binary : input.operation.isShift = false) :
    output.destination.toBitVec = Verification.byteOperation input.operation.tag input.left input.right := by
  have bytes := byte_result (by omega) h interface mapping binary
  have selected : w 11 = 0 ∧ w 12 = 1 := by simpa [binary] using interface.selected
  have low := Verification.assertion_of_holds h ⟨41, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨42, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected.1, selected.2] at low high
  have packed (a b c : ZMod p) (ha : a.val < 256) (hb : b.val < 256)
      (eq : a + 256 * b - c = 0) : c.val = a.val + 256 * b.val := by
    exact byte_pair_value hp a b c ha hb (by linear_combination eq)
  let result := Verification.byteOperation input.operation.tag input.left input.right
  have bounds (i : Fin 4) : (w (36 + i.val)).val < 256 := by
    rw [bytes i]; exact (result.extractLsb' (8 * i.val) 8).isLt
  have lo := packed (w 36) (w 37) (w 31) (bounds 0) (bounds 1)
    (by simpa [sub_eq_add_neg] using low)
  have hi := packed (w 38) (w 39) (w 32) (bounds 2) (bounds 3)
    (by simpa [sub_eq_add_neg] using high)
  apply BitVec.eq_of_toNat_eq
  change output.destination.value % 4294967296 = result.toNat
  have value : output.destination.value = result.toNat := by
    rw [Word.value, mapping.outputLo, mapping.outputHi, lo, hi]
    have b0 : (w 36).val = (result.extractLsb' 0 8).toNat := bytes 0
    have b1 : (w 37).val = (result.extractLsb' 8 8).toNat := bytes 1
    have b2 : (w 38).val = (result.extractLsb' 16 8).toNat := bytes 2
    have b3 : (w 39).val = (result.extractLsb' 24 8).toNat := bytes 3
    rw [b0, b1, b2, b3]
    rw [bytes_value result]
    simp only [limbBase]
    ring
  rw [value, Nat.mod_eq_of_lt result.isLt]

private theorem shift_count {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {input : Input} {output : Sail.Output} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (interface : RowInterfaces input output w)
    (mapping : RowWordMapping input output w)
    (shift : input.operation.isShift = true) :
    (w 35 + w 8).val =
      (if input.operation = .rev8 then 0 else
        (if input.immediate then input.encodedImmediate.extractLsb' 0 5
          else input.right.extractLsb' 0 5).toNat) := by
  have selected : w 11 = 1 ∧ w 12 = 0 := by simpa [shift] using interface.selected
  have truncated := (shift_amount hp h selected).2.2
  by_cases reverse : input.operation = .rev8
  · have source : w 25 = 0 := by simpa [reverse] using mapping.shiftLowByte shift
    have immediate : w 8 = 0 := by simpa [reverse] using mapping.shiftImmediate shift
    rw [source] at truncated
    norm_num at truncated
    simp [reverse, immediate, truncated]
  simp only [reverse, if_false]
  cases kind : input.immediate
  · have source : w 25 = ((input.right.extractLsb' 0 8).toNat : ZMod p) := by
      simpa [kind, reverse] using mapping.shiftLowByte shift
    have immediate : w 8 = 0 := by simpa [kind, reverse] using mapping.shiftImmediate shift
    have castValue : ((input.right.extractLsb' 0 8).toNat : ZMod p).val =
        (input.right.extractLsb' 0 8).toNat := by
      have bound := (input.right.extractLsb' 0 8).isLt
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [source, castValue] at truncated
    rw [immediate, add_zero, truncated]
    exact Verification.low_byte_shift_amount input.right
  · have source : w 25 = 0 := by simpa [kind, reverse] using mapping.shiftLowByte shift
    have immediate : w 8 = ((input.encodedImmediate.extractLsb' 0 5).toNat : ZMod p) := by
      simpa [kind, reverse] using mapping.shiftImmediate shift
    rw [source] at truncated
    norm_num at truncated
    have zero : w 35 = 0 := truncated
    simp only [if_true, zero, zero_add, immediate]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by
      have := (input.encodedImmediate.extractLsb' 0 5).isLt; omega)]

private theorem shifted_destination {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    {input : Input} {output : Sail.Output} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (interface : RowInterfaces input output w)
    (mapping : RowWordMapping input output w)
    (shift : input.operation.isShift = true) :
    output.destination.toBitVec = Verification.shiftOperation input.operation.tag input.left
      (if input.operation = .rev8 then 0 else
        (if input.immediate then input.encodedImmediate.extractLsb' 0 5
          else input.right.extractLsb' 0 5).toNat) := by
  have selected : w 11 = 1 ∧ w 12 = 0 := by simpa [shift] using interface.selected
  have code : (w 10).val = input.operation.tag := by
    have bound : input.operation.tag < 8 := by cases input.operation <;> decide
    rw [interface.funct3, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have valid : (w 10).val = 1 ∨ (w 10).val = 2 ∨ (w 10).val = 3 ∨ (w 10).val = 5 := by
    rw [code]
    cases op : input.operation <;> simp_all [Operation.tag, Operation.isShift]
  have reverse : (w 10).val = 5 → (w 35 + w 8).val = 0 := by
    intro rev
    have op : input.operation = .rev8 := by
      rw [code] at rev
      cases operation : input.operation <;> simp_all [Operation.tag]
    rw [shift_count (by omega) h interface mapping shift]
    simp [op]
  have result := shift_destination hp input.left h selected valid reverse mapping.leftBytes
  rw [code, shift_count (by omega) h interface mapping shift] at result
  simpa [Word.toBitVec, Word.value, mapping.outputLo, mapping.outputHi] using result

private theorem sail_shift_left (x : BitVec 32) (amount : BitVec n) :
    _root_.Sail.shift_bits_left x amount = x <<< amount.toNat := rfl

private theorem sail_shift_right (x : BitVec 32) (amount : BitVec n) :
    _root_.Sail.shift_bits_right x amount = x >>> amount.toNat := rfl

private theorem sail_shift_arithmetic (x : BitVec 32) (amount : BitVec n) :
    SailRV32.Functions.shift_bits_right_arith x amount = x.sshiftRight amount.toNat := rfl

/-- One shared native Sail claim covers the binary and shift branches. Counts
    come from the imported truncation query and decoder operand mapping. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) :
    rowCircuitModel.SoundnessUnder (RowInterfaces (p := p)) spec := by
  intro input output w ⟨interface, h, mapping⟩
  have pc := pc_successor (by omega) inverse h
    ⟨mapping.pcLo, mapping.pcHi, mapping.finalPCLo, mapping.finalPCHi⟩ interface.initialPCBound
  apply Sail.retire_of_destination interface.pcRead pc.2.2
  let prepared : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have left := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs1 interface.leftRead
  have same : run (execution input) prepared =
      run (Sail.writeResult input.rd output.destination) prepared := by
    cases operation : input.operation <;> cases immediate : input.immediate
    all_goals
      simp only [execution, operation, immediate, Sail.writeResult,
        SailRV32.Functions.execute_RTYPE, SailRV32.Functions.execute_ITYPE,
        SailRV32.Functions.execute_SHIFTIOP, SailRV32.Functions.execute_REV8,
        freeM_bind_assoc, freeM_pure_bind]
      rw [run_bind_of_ok _ _ _ _ _ left]
    all_goals first
      | (have reverse : input.operation = .rev8 := by rw [operation]
         have dest := shifted_destination hp h interface mapping (by rw [operation]; rfl)
         rw [dest]
         simp [Verification.shiftOperation, reverse, Operation.tag, prepared])
      | (have right := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs2
           (interface.rightRead immediate (by rw [operation]; decide))
         rw [run_bind_of_ok _ _ _ _ _ right]
         first
           | (have dest := destination (by omega) h interface mapping (by rw [operation]; rfl)
              rw [dest]; simp [Verification.byteOperation, operation, Operation.tag, prepared])
           | (have dest := shifted_destination hp h interface mapping (by rw [operation]; rfl)
              rw [dest]
              simp [Verification.shiftOperation, operation, Operation.tag, immediate, prepared,
                sail_shift_left, sail_shift_right, sail_shift_arithmetic,
                _root_.Sail.BitVec.extractLsb, SailRV32.Functions.log2_xlen,
                BitVec.extractLsb]))
      | (have binary : input.operation.isShift = false := by rw [operation]; rfl
         have dest := destination (by omega) h interface mapping binary
         rw [dest, interface.signExtension immediate binary]
         simp [Verification.byteOperation, operation, Operation.tag, prepared])
      | (have dest := shifted_destination hp h interface mapping (by rw [operation]; rfl)
         rw [dest]
         simp [Verification.shiftOperation, operation, Operation.tag, immediate, prepared,
           sail_shift_left, sail_shift_right, sail_shift_arithmetic,
           _root_.Sail.BitVec.extractLsb, SailRV32.Functions.log2_xlen])
  obtain ⟨after, write⟩ := Sail.write_success input.rd output.destination.toBitVec prepared
  have projected : run (Sail.writeResult input.rd output.destination) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
    unfold Sail.writeResult
    rw [run_bind_of_ok _ _ _ _ _ write]
    rfl
  exact ⟨after, same.trans projected, projected⟩

end Airbender.ShiftBinop.Proofs
