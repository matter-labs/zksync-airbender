import Airbender.Review.Circuits.ReducedMachine.BitwiseTheorems
import Airbender.Review.Circuits.ReducedMachine.Tables.NativeBitwiseTheorems

namespace Tests.NativeReducedBitwise
open Airbender Arithmetic Trace ReducedMachine Native Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native masks differ from the old split family; original decoding is separate. -/
theorem masks : bitwiseMask false = 33 ∧ bitwiseMask true = 35 := ⟨rfl,rfl⟩

/-- Lift every independently certified actual byte row at its real native pool
    offset. These are table members, not full117-equation instruction fixtures. -/
theorem actual_byte_rows (kind : BinaryKind) (i : Fin 65536) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      (((binaryRow kind i).push kind.tag).map (Nat.cast : Nat → ZMod mersenne31Modulus)) := by
  cases kind
  · refine ⟨⟨i.val + 1,by change i.val + 1 < 5771521; have := i.isLt; omega⟩,?_⟩
    change _ = (NativeFixed.rowNat ⟨i.val + 1,_⟩).map Nat.cast
    have h0 : ¬ i.val + 1 < 1 := by have := i.isLt; omega
    have selected : i.val + 1 < 65537 := by have := i.isLt; omega
    rw [NativeFixed.rowNat,dif_neg h0,dif_pos selected]
    simp only [Nat.add_sub_cancel_right]
    have rows := congrArg (fun data : Setup.TableData 4 =>
      data.columns.map (fun column => (column.get? i.val).getD 0)) NativeBitwiseDataProofs.xor_data
    have exactRow := rows.trans (BinaryProofs.native_rows .xor i)
    exact congrArg (fun v : Vector Nat 4 => v.map (Nat.cast : Nat → ZMod mersenne31Modulus)) exactRow.symm
  · refine ⟨⟨i.val + 65537,by change i.val + 65537 < 5771521; have := i.isLt; omega⟩,?_⟩
    change _ = (NativeFixed.rowNat ⟨i.val + 65537,_⟩).map Nat.cast
    have h0 : ¬ i.val + 65537 < 1 := by have := i.isLt; omega
    have h1 : ¬ i.val + 65537 < 65537 := by have := i.isLt; omega
    have selected : i.val + 65537 < 131073 := by have := i.isLt; omega
    rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_pos selected]
    simp only [Nat.add_sub_cancel_right]
    have rows := congrArg (fun data : Setup.TableData 4 =>
      data.columns.map (fun column => (column.get? i.val).getD 0)) NativeBitwiseDataProofs.or_data
    have exactRow := rows.trans (BinaryProofs.native_rows .or i)
    exact congrArg (fun v : Vector Nat 4 => v.map (Nat.cast : Nat → ZMod mersenne31Modulus)) exactRow.symm
  · refine ⟨⟨i.val + 131073,by change i.val + 131073 < 5771521; have := i.isLt; omega⟩,?_⟩
    change _ = (NativeFixed.rowNat ⟨i.val + 131073,_⟩).map Nat.cast
    have h0 : ¬ i.val + 131073 < 1 := by have := i.isLt; omega
    have h1 : ¬ i.val + 131073 < 65537 := by have := i.isLt; omega
    have h2 : ¬ i.val + 131073 < 131073 := by have := i.isLt; omega
    have selected : i.val + 131073 < 196609 := by have := i.isLt; omega
    rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_pos selected]
    simp only [Nat.add_sub_cancel_right]
    have rows := congrArg (fun data : Setup.TableData 4 =>
      data.columns.map (fun column => (column.get? i.val).getD 0)) NativeBitwiseDataProofs.and_data
    have exactRow := rows.trans (BinaryProofs.native_rows .and i)
    exact congrArg (fun v : Vector Nat 4 => v.map (Nat.cast : Nat → ZMod mersenne31Modulus)) exactRow.symm

private def boundaryLeft (i : Fin 3) : Nat := #v[0,128,255][i]
private def boundaryRight (i : Fin 3) : Nat := #v[0,127,255][i]
private def boundaryOutput (kind : BinaryKind) (i : Fin 3) : Nat :=
  (match kind with | .xor => #v[0,255,0] | .or => #v[0,255,255] | .and => #v[0,0,255])[i]

/-- Independent expected byte values at zero, the crossing bit boundary and
    both maximal bytes. These are actual pool members for every operation. -/
theorem boundary_rows (kind : BinaryKind) (i : Fin 3) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      #v[(boundaryLeft i : ZMod mersenne31Modulus),(boundaryRight i : ZMod mersenne31Modulus),
        (boundaryOutput kind i : ZMod mersenne31Modulus),(kind.tag : ZMod mersenne31Modulus)] := by
  let n : Fin 65536 := #v[0,32895,65535][i]
  have values : (((binaryRow kind n).push kind.tag).map (Nat.cast : Nat → ZMod mersenne31Modulus)) =
      #v[(boundaryLeft i : ZMod mersenne31Modulus),(boundaryRight i : ZMod mersenne31Modulus),
        (boundaryOutput kind i : ZMod mersenne31Modulus),(kind.tag : ZMod mersenne31Modulus)] := by
    cases kind <;> fin_cases i <;> decide +kernel
  have member := actual_byte_rows kind n
  rw [values] at member
  exact member

theorem corrupted_xor_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[128,127,254,4] := by
  intro member
  have output := (NativeFixed.bitwise_implementation .xor _ member rfl).2.2.2
  exact (by decide +kernel : ¬ (BitVec.ofNat 8 (254 : ZMod mersenne31Modulus).val) =
    byteOperation BinaryKind.xor.tag (BitVec.ofNat 8 (128 : ZMod mersenne31Modulus).val)
      (BitVec.ofNat 8 (127 : ZMod mersenne31Modulus).val)) output

theorem wrong_operation_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[255,255,0,6] := by
  intro member
  have output := (NativeFixed.bitwise_implementation .or _ member rfl).2.2.2
  exact (by decide +kernel : ¬ (BitVec.ofNat 8 (0 : ZMod mersenne31Modulus).val) =
    byteOperation BinaryKind.or.tag (BitVec.ofNat 8 (255 : ZMod mersenne31Modulus).val)
      (BitVec.ofNat 8 (255 : ZMod mersenne31Modulus).val)) output

theorem oversized_byte_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[256,0,0,7] := by
  intro member
  have bound := (NativeFixed.bitwise_implementation .and _ member rfl).1
  exact (by decide +kernel : ¬ (256 : ZMod mersenne31Modulus).val < 256) bound

/-- Native immediate routing keeps the actual readonly rs2/register-space port. -/
theorem immediate_port {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = 33) : source2 w = #v[w 9,w 10] ∧
      w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1 ∧ importedConstraintsMemoryPorts[1].writeValue = none := by
  have port := NativeBitwiseFieldProofs.source_port holds false mask
  exact ⟨NativeBitwiseFieldProofs.source holds false mask,port.1,port.2.1,port.2.2,rfl⟩

/-- Discarding an actual write retains all candidate/source/byte obligations. -/
theorem discarded_participation {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (kind : BinaryKind) (useRegister : Bool)
    (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.tag : ZMod mersenne31Modulus)) (zero : rdZeroFlag w = 1) :
    rdWrite w = #v[0,0] ∧ (sourceWord w).Bounded ∧ (operandWord w).Bounded ∧ (candidateWord w).Bounded := by
  have value := bitwise_result holds kind useRegister mask tag
  refine ⟨?_,value.1,value.2.1,value.2.2.1⟩
  rw [(bitwise_masked_write holds useRegister mask).2]
  simp [zero,arithmeticCandidate]

/-- Complete native byte constraints reject the formerly unchecked source-low
    overflow locally for bitwise rows, without a supplied read-range premise. -/
theorem oversized_source_rejected {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (kind : BinaryKind) (useRegister : Bool)
    (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.tag : ZMod mersenne31Modulus)) : (w 35).val < 65536 :=
  (bitwise_result holds kind useRegister mask tag).1.1

/-- Independent numerical cases retain the sign bit above M31 and both limbs.
    These are conditional native consequences, not complete execution fixtures. -/
theorem cross_limb_results {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (kind : BinaryKind) (useRegister : Bool)
    (mask : w 12 = (bitwiseMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.tag : ZMod mersenne31Modulus))
    (source : sourceWord w = ⟨65535,32768⟩) (operand : operandWord w = ⟨65535,0⟩) :
    (candidateWord w).toBitVec = match kind with
      | .xor => 0x80000000 | .or => 0x8000ffff | .and => 0x0000ffff := by
  have value := (bitwise_result holds kind useRegister mask tag).2.2.2
  rw [source,operand] at value
  cases kind <;> simpa [byteOperation,BinaryKind.tag,Word.toBitVec,Word.value,limbBase] using value

end Tests.NativeReducedBitwise
