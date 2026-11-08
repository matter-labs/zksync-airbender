module
public import Human.ISA.RV32
public import Slop.ShiftBinop.Ports
public import Slop.ShiftBinop.RVQuery

@[expose] public section

/-! Row-level XOR/OR/AND, SLL/SRL/SRA and REV8 result in RV32 terms: the imported constraints with the decoder's
    selectors, tag and immediate columns force the destination word to be `RV.alu` (or `RV.rev8`) of the two read
    ports' words, or of the first and the immediate. Statements are Sail-free; the proofs reuse the row calculation
    lemmas of `Soundness.lean`, `Shifts.lean` and `Ports.lean` (whose BitVec helpers are `shiftOperation`, built on
    `RV.rev8`, and `BitVec.signExtend`). -/

namespace Airbender.ShiftBinop

/-- The `RV.Op` of each ALU operation of the circuit (REV8 is not an `RV.alu` operation). -/
def Operation.rvOp : Operation → RV.Op
  | .xor => .xor | .or => .or | .and => .and | .sll => .sll | .srl => .srl | .sra => .sra | .rev8 => .add

end Airbender.ShiftBinop

namespace Airbender.ShiftBinop.Proofs
open Airbender.Arithmetic Trace

/-- The second ALU operand: the second source word for register forms, the sign-extended immediate for binary
    immediates, the zero-extended low five bits of the encoding for immediate shifts. -/
def rvOperand (operation : Operation) (immediate : Bool) (imm : BitVec 12) (y : BitVec 32) : BitVec 32 :=
  if immediate then
    if operation.isShift then (imm.extractLsb' 0 5).zeroExtend 32 else imm.signExtend 32
  else y

/-- The RV result of a row with first source `x` and second source `y`. -/
def rvValue (operation : Operation) (immediate : Bool) (imm : BitVec 12) (x y : BitVec 32) : BitVec 32 :=
  if operation = .rev8 then RV.rev8 x else RV.alu operation.rvOp x (rvOperand operation immediate imm y)

/-- Binary rows: bounded byte operands give the destination word, byte by byte (as `destination` of
    `Soundness.lean`, on words instead of a Sail input). -/
theorem rv_binary_destination {p : Nat} [Fact p.Prime] (hp : 65536 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 1) (tag : Nat)
    (validTag : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (tag : ZMod p)) (x y : BitVec 32)
    (leftBytes : ∀ i : Fin 4, w (19 + i.val) = ((x.extractLsb' (8 * i.val) 8).toNat : ZMod p))
    (rightBytes : ∀ i : Fin 4, w (25 + i.val) +
      (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35) =
      ((y.extractLsb' (8 * i.val) 8).toNat : ZMod p)) :
    (Word.mk (w 31).val (w 32).val).toBitVec = Verification.byteOperation tag x y := by
  have bytes : ∀ i : Fin 4, (w (36 + i.val)).val =
      ((Verification.byteOperation tag x y).extractLsb' (8 * i.val) 8).toNat := by
    intro i
    have values := binary_query_values (by omega) h selected tag validTag funct3 i
    rw [leftBytes i, rightBytes i] at values
    have lb := (x.extractLsb' (8 * i.val) 8).isLt
    have rb := (y.extractLsb' (8 * i.val) 8).isLt
    have lc : ((x.extractLsb' (8 * i.val) 8).toNat : ZMod p).val = (x.extractLsb' (8 * i.val) 8).toNat := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have rc : ((y.extractLsb' (8 * i.val) 8).toNat : ZMod p).val = (y.extractLsb' (8 * i.val) 8).toNat := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [lc, rc] at values
    have eq := congrArg BitVec.toNat values.2.2.2
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt values.2.2.1,
      BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq] at eq
    rw [eq]
    rcases validTag with rfl | rfl | rfl <;>
      simp [Verification.byteOperation, BitVec.extractLsb'_xor, BitVec.extractLsb'_or, BitVec.extractLsb'_and]
  have low := Verification.assertion_of_holds h ⟨41, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨42, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected.1, selected.2] at low high
  have packed (a b c : ZMod p) (ha : a.val < 256) (hb : b.val < 256)
      (eq : a + 256 * b - c = 0) : c.val = a.val + 256 * b.val := by
    exact byte_pair_value hp a b c ha hb (by linear_combination eq)
  let result := Verification.byteOperation tag x y
  have bounds (i : Fin 4) : (w (36 + i.val)).val < 256 := by
    rw [bytes i]; exact (result.extractLsb' (8 * i.val) 8).isLt
  have lo := packed (w 36) (w 37) (w 31) (bounds 0) (bounds 1)
    (by simpa [sub_eq_add_neg] using low)
  have hi := packed (w 38) (w 39) (w 32) (bounds 2) (bounds 3)
    (by simpa [sub_eq_add_neg] using high)
  apply BitVec.eq_of_toNat_eq
  change (Word.mk (w 31).val (w 32).val).value % 4294967296 = result.toNat
  have value : (Word.mk (w 31).val (w 32).val).value = result.toNat := by
    rw [Word.value]
    dsimp only
    rw [lo, hi]
    have b0 : (w 36).val = (result.extractLsb' 0 8).toNat := bytes 0
    have b1 : (w 37).val = (result.extractLsb' 8 8).toNat := bytes 1
    have b2 : (w 38).val = (result.extractLsb' 16 8).toNat := bytes 2
    have b3 : (w 39).val = (result.extractLsb' 24 8).toNat := bytes 3
    rw [b0, b1, b2, b3]
    rw [bytes_value result]
    simp only [limbBase]
    ring
  rw [value, Nat.mod_eq_of_lt result.isLt]

/-- Register-form binary rows: the destination is `byteOperation` of the two read ports' words. -/
theorem rv_binary_register {p : Nat} [Fact p.Prime] (hp : 65536 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 1) (tag : Nat)
    (validTag : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (tag : ZMod p))
    (immediate : w 8 = 0 ∧ w 9 = 0) :
    (Word.mk (w 31).val (w 32).val).toBitVec = Verification.byteOperation tag
      (memoryWord (importedConstraintsMemoryPorts[0].readCode w))
      (memoryWord (importedConstraintsMemoryPorts[1].readCode w)) :=
  rv_binary_destination hp h selected tag validTag funct3 _ _
    (binary_left_bytes (by omega) h selected tag validTag funct3)
    (binary_register_right_bytes (by omega) h selected tag validTag funct3 immediate)

/-- Immediate-form binary rows (second port reads x0 as zero): the destination is `byteOperation` of the first read
    port's word and the sign-extended immediate. -/
theorem rv_binary_immediate {p : Nat} [Fact p.Prime] (hp : 65536 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 1) (tag : Nat)
    (validTag : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (tag : ZMod p)) (imm : BitVec 12)
    (immediate : w 8 = ((binaryImmediate (imm.signExtend 32)).lo : ZMod p) ∧
      w 9 = ((binaryImmediate (imm.signExtend 32)).hi : ZMod p))
    (zeroRead : importedConstraintsMemoryPorts[1].readCode w = 0) :
    (Word.mk (w 31).val (w 32).val).toBitVec = Verification.byteOperation tag
      (memoryWord (importedConstraintsMemoryPorts[0].readCode w)) (imm.signExtend 32) := by
  have packed : w 8 = ((imm.signExtend 32).extractLsb' 0 8).toNat ∧
      w 9 = ((imm.signExtend 32).extractLsb' 8 8).toNat := by
    simpa [binaryImmediate, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] using immediate
  exact rv_binary_destination hp h selected tag validTag funct3 _ _
    (binary_left_bytes (by omega) h selected tag validTag funct3)
    (binary_immediate_right_bytes (by omega) h selected tag validTag funct3 imm packed
      (by simpa only [show Nat.pair 0 0 = 0 by decide] using zeroRead))

/-- Register-form shifts: the amount is the low five bits of the second read port's word. -/
theorem rv_shift_register_amount {p : Nat} [Fact p.Prime] (hp : 65536 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 1 ∧ w 12 = 0) (immediate : w 8 = 0) :
    (w 35 + w 8).val = ((memoryWord (importedConstraintsMemoryPorts[1].readCode w)).extractLsb' 0 5).toNat := by
  have truncated := (shift_amount (by omega) h selected).2.2
  have source := shift_right_low_byte (by omega) h selected
  let y := memoryWord (importedConstraintsMemoryPorts[1].readCode w)
  have castValue : ((y.extractLsb' 0 8).toNat : ZMod p).val = (y.extractLsb' 0 8).toNat := by
    have bound := (y.extractLsb' 0 8).isLt
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [source, castValue] at truncated
  rw [immediate, add_zero, truncated]
  exact Verification.low_byte_shift_amount y

/-- Immediate shifts and REV8 (second port reads x0 as zero): the amount is the immediate column. -/
theorem rv_shift_immediate_amount {p : Nat} [Fact p.Prime] (hp : 65536 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 1 ∧ w 12 = 0) (zeroRead : importedConstraintsMemoryPorts[1].readCode w = 0)
    {k : Nat} (small : k < 32) (immediate : w 8 = (k : ZMod p)) :
    (w 35 + w 8).val = k := by
  have truncated := (shift_amount (by omega) h selected).2.2
  have source := shift_right_low_byte (by omega) h selected
  rw [zeroRead, show memoryWord 0 = (0 : BitVec 32) by decide] at source
  rw [source] at truncated
  norm_num at truncated
  have zero : w 35 = 0 := truncated
  rw [zero, zero_add, immediate, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-- Shift rows: the destination is `shiftOperation` of the first read port's word by the row's amount. -/
theorem rv_shift_value {p : Nat} [Fact p.Prime] (hp : 262144 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 1 ∧ w 12 = 0) (tag : Nat)
    (valid : tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 5) (funct3 : w 10 = (tag : ZMod p))
    {n : Nat} (amount : (w 35 + w 8).val = n) (reverse : tag = 5 → n = 0) :
    (Word.mk (w 31).val (w 32).val).toBitVec = Verification.shiftOperation tag
      (memoryWord (importedConstraintsMemoryPorts[0].readCode w)) n := by
  have code : (w 10).val = tag := by
    have bound : tag < 8 := by omega
    rw [funct3, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have result := shift_destination hp _ h selected (code ▸ valid)
    (fun rev => amount.trans (reverse (code ▸ rev))) (shift_left_bytes (by omega) h selected)
  rw [code, amount] at result
  exact result

/-- One row with the decoder's selectors, tag and immediate columns: the destination word is the RV result of the
    two read ports' words (`rvValue`). For immediate forms and REV8 the second port reads x0, as zero. -/
theorem rv_row_value {p : Nat} [Fact p.Prime] (hp : 262144 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (operation : Operation) (immediate : Bool) (imm : BitVec 12)
    (selected : if operation.isShift then w 11 = 1 ∧ w 12 = 0 else w 11 = 0 ∧ w 12 = 1)
    (funct3 : w 10 = (operation.tag : ZMod p))
    (immediateLo : w 8 = ((rvImmediate operation immediate imm).lo : ZMod p))
    (immediateHi : w 9 = ((rvImmediate operation immediate imm).hi : ZMod p))
    (zeroRead : (immediate || operation = .rev8) = true → importedConstraintsMemoryPorts[1].readCode w = 0) :
    (Word.mk (w 31).val (w 32).val).toBitVec = rvValue operation immediate imm
      (memoryWord (importedConstraintsMemoryPorts[0].readCode w))
      (memoryWord (importedConstraintsMemoryPorts[1].readCode w)) := by
  have small5 : (imm.extractLsb' 0 5).toNat < 32 := (imm.extractLsb' 0 5).isLt
  cases operation <;> cases immediate <;>
    simp only [Operation.isShift, Operation.tag, ite_true, Bool.false_eq_true, ite_false] at selected funct3 <;>
    simp only [rvImmediate, Operation.isShift, reduceCtorEq, ite_true, ite_false, Bool.false_eq_true]
      at immediateLo immediateHi zeroRead
  -- Register-form binary operations.
  case xor.false | or.false | and.false =>
    rw [rv_binary_register (by omega) h selected _ (by decide) funct3 ⟨by simpa using immediateLo,
      by simpa using immediateHi⟩]
    rfl
  -- Immediate-form binary operations.
  case xor.true | or.true | and.true =>
    rw [rv_binary_immediate (by omega) h selected _ (by decide) funct3 imm ⟨immediateLo, immediateHi⟩
      (zeroRead (by decide))]
    rfl
  -- Register-form shifts.
  case sll.false | srl.false | sra.false =>
    rw [rv_shift_value hp h selected _ (by decide) funct3
      (rv_shift_register_amount (by omega) h selected (by simpa using immediateLo)) (fun e => absurd e (by decide))]
    simp [rvValue, rvOperand, Operation.rvOp, RV.alu, Verification.shiftOperation]
  -- Immediate shifts.
  case sll.true | srl.true | sra.true =>
    rw [rv_shift_value hp h selected _ (by decide) funct3
      (rv_shift_immediate_amount (by omega) h selected (zeroRead (by decide)) small5 immediateLo)
      (fun e => absurd e (by decide))]
    simp [rvValue, rvOperand, Operation.rvOp, Operation.isShift, RV.alu, Verification.shiftOperation]
  -- REV8.
  all_goals
    rw [rv_shift_value hp h selected _ (by decide) funct3
      (rv_shift_immediate_amount (by omega) h selected (zeroRead (by decide)) (by decide : 0 < 32)
        (by simpa using immediateLo)) (fun _ => rfl)]
    simp [rvValue, Verification.shiftOperation]

end Airbender.ShiftBinop.Proofs
