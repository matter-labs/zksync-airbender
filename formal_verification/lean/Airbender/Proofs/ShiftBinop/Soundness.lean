import Airbender.Review.ShiftBinop.Model
import Airbender.Proofs.ShiftBinop
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

private theorem byte_result {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {input : Input} {output : Sail.Output} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (interface : InterfaceAssumptions input output w)
    (mapping : WordMapping input output w) :
    ∀ i : Fin 4, (w (36 + i.val)).val =
      ((Verification.byteOperation input.operation.tag input.left input.right).extractLsb'
        (8 * i.val) 8).toNat := by
  intro i
  have wires := wiring h interface.selected i
  have query := Verification.lookup_of_holds h
    ⟨3 + i.val, by rw [lookup_count]; have := i.isLt; omega⟩
  have validTag : input.operation.tag = 4 ∨ input.operation.tag = 6 ∨ input.operation.tag = 7 := by
    cases input.operation <;> simp [Operation.tag]
  have values : (w (19 + i.val)).val < 256 ∧
      (w (25 + i.val) + (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35)).val < 256 ∧
      (w (36 + i.val)).val < 256 ∧ BitVec.ofNat 8 (w (36 + i.val)).val =
        Verification.byteOperation input.operation.tag (BitVec.ofNat 8 (w (19 + i.val)).val)
          (BitVec.ofNat 8 (w (25 + i.val) +
            (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35)).val) := by
    fin_cases i
    all_goals
      norm_num only at wires
      have value := Verification.binary_lookup hp query input.operation.tag validTag
        (by simpa [Expression.eval, Verification.environment, wires.2.2.2] using interface.funct3)
      simpa [Expression.eval, Verification.environment, wires.1, wires.2.1,
        wires.2.2.1] using value
  have left := mapping.leftBytes i
  have right := mapping.rightBytes i
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
  cases input.operation <;>
    simp [Verification.byteOperation, Operation.tag, BitVec.extractLsb'_xor,
      BitVec.extractLsb'_or, BitVec.extractLsb'_and]

private theorem destination {p : Nat} [Fact p.Prime] (hp : 65536 < p)
    {input : Input} {output : Sail.Output} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (interface : InterfaceAssumptions input output w)
    (mapping : WordMapping input output w) :
    output.destination.toBitVec = Verification.byteOperation input.operation.tag input.left input.right := by
  have bytes := byte_result (by omega) h interface mapping
  have low := Verification.assertion_of_holds h ⟨41, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨42, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, interface.selected.1, interface.selected.2] at low high
  have packed (a b c : ZMod p) (ha : a.val < 256) (hb : b.val < 256)
      (eq : a + 256 * b - c = 0) : c.val = a.val + 256 * b.val := by
    have field : c = a + 256 * b := by linear_combination -eq
    rw [field, ZMod.val_add, ZMod.val_mul]
    norm_num only [ZMod.val_natCast, ZMod.val_ofNat]
    rw [Nat.mod_eq_of_lt (show 256 < p by omega),
      Nat.mod_eq_of_lt (show 256 * b.val < p by omega),
      Nat.mod_eq_of_lt (show a.val + 256 * b.val < p by omega)]
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

theorem soundness {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec := by
  intro input output w ⟨interface, h, mapping⟩
  have dest := destination (by omega) h interface mapping
  have pc := pc_successor hp inverse h
    ⟨mapping.pcLo, mapping.pcHi, mapping.finalPCLo, mapping.finalPCHi⟩ interface.initialPCBound
  apply Sail.retire_of_destination interface.pcRead pc.2.2
  let prepared : Sail.State :=
    { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have left := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs1 interface.leftRead
  have same : run (execution input) prepared =
      run (Sail.writeResult input.rd output.destination) prepared := by
    unfold execution Sail.writeResult
    cases immediate : input.immediate
    · have right := Sail.rX_nextPC (pc := output.pc.toBitVec) input.rs2 (interface.rightRead immediate)
      simp only [Bool.false_eq_true, if_false]
      cases operation : input.operation <;>
        simp only [SailRV32.Functions.execute_RTYPE, freeM_bind_assoc, freeM_pure_bind] <;>
        rw [run_bind_of_ok _ _ _ _ _ left, run_bind_of_ok _ _ _ _ _ right]
      all_goals rw [dest]; simp [Verification.byteOperation, operation, Operation.tag, prepared]
    · simp only [if_true]
      cases operation : input.operation <;>
        simp only [SailRV32.Functions.execute_ITYPE, freeM_bind_assoc, freeM_pure_bind] <;>
        rw [run_bind_of_ok _ _ _ _ _ left]
      all_goals rw [dest, interface.signExtension immediate]
      all_goals simp [Verification.byteOperation, operation, Operation.tag, prepared]
  obtain ⟨after, write⟩ := Sail.write_success input.rd output.destination.toBitVec prepared
  have projected : run (Sail.writeResult input.rd output.destination) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
    unfold Sail.writeResult
    rw [run_bind_of_ok _ _ _ _ _ write]
    rfl
  exact ⟨after, same.trans projected, projected⟩

end Airbender.ShiftBinop.Proofs
