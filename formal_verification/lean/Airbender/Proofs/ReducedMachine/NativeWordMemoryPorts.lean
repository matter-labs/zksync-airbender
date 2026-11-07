import Airbender.Review.Helpers.Memory.ReducedMachineWordMemory
import Airbender.Proofs.ReducedMachine.NativeWordMemoryDecoder
import Airbender.Proofs.ReducedMachine.NativeWordMemoryShape
import Airbender.Proofs.ReducedMachine.NativeShiftPorts
import Airbender.Proofs.Trace.InitialImage

namespace Airbender.ReducedMachine.NativeWordMemoryPortProofs
open Native Trace Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Unchanged actual metadata: these are readonly clock refreshes in either
    address space. No native memory event is omitted. -/
theorem readonly_sources : importedConstraintsMemoryPorts[0].writeValue = none ∧
    importedConstraintsMemoryPorts[1].writeValue = none := NativeShiftPortProofs.readonly_sources

theorem address_roundtrip {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table)) :
    Word.ofBitVec (wordMemoryAddressWord w).toBitVec = wordMemoryAddressWord w := by
  have bound := NativeWordMemoryNumericalProofs.address_bounds holds
  apply Word.eq_of_value (Word.ofBitVec_bound _) bound
  rw [Word.ofBitVec_value,Word.toBitVec_toNat bound]

/-- Original public fields and fresh actual load/store equations bind every
    register-or-memory port, including the retained ROM shadow and store OLDREAD. -/
theorem addresses {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    ∀ i : Fin 3, importedConstraintsMemoryPorts[i].address.code w =
      (wordMemoryPortCells w entry)[i].addressCode := by
  have decoded := NativeWordMemoryDecoderProofs.decoded_fields fields query
  have routing := NativeWordMemoryFieldProofs.routing holds entry.data.family decoded.mask
  have rs1 : (w 5).val = entry.data.rs1.toNat := by
    rw [decoded.rs1,ZMod.val_natCast_of_lt (lt_trans entry.data.rs1.isLt (by decide))]
  have rs2 : (w 6).val = entry.data.rs2.toNat := by
    rw [decoded.rs2,ZMod.val_natCast_of_lt (lt_trans entry.data.rs2.isLt (by decide))]
  have rd : (w 7).val = entry.data.rd.toNat := by
    change (rdIndex w).val = _
    rw [decoded.rd,ZMod.val_natCast_of_lt (lt_trans entry.data.rd.isLt (by decide))]
  have canonical := address_roundtrip holds
  change Word.ofBitVec (⟨(w 61).val,(w 62).val⟩ : Word).toBitVec = ⟨(w 61).val,(w 62).val⟩ at canonical
  have oneVal : (1 : ZMod mersenne31Modulus).val = 1 := by decide
  cases mode : entry.data.family
  · have mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus) := by simpa [mode] using decoded.mask
    have access := NativeWordMemoryAccessProofs.load_access holds mask
    have lo : w 39 = w 61 := by simpa using congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) access.shadowAddress
    have hi : w 40 = w 62 := by simpa using congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) access.shadowAddress
    have rdLo : w 45 = w 7 := by simpa using congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) access.destination
    have rdHi : w 46 = 0 := by simpa using congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) access.destination
    simp only [mode] at routing
    intro i
    fin_cases i <;> simp [wordMemoryPortCells,mode,importedConstraintsMemoryPorts,
      MemoryAddress.code,pairCode,Cell.addressCode,routing.secondSpace,routing.thirdSpace,
      canonical,oneVal,wordMemoryAddressWord,rs1,rd,lo,hi,rdLo,rdHi]
  · have mask : w 12 = (wordMemoryMask true : ZMod mersenne31Modulus) := by simpa [mode] using decoded.mask
    have access := NativeWordMemoryAccessProofs.store_access holds mask
    have lo : w 39 = w 6 := by simpa using congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) access.sourceAddress
    have hi : w 40 = 0 := by simpa using congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) access.sourceAddress
    have memLo : w 45 = w 61 := by simpa using congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) access.destination
    have memHi : w 46 = w 62 := by simpa using congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) access.destination
    simp only [mode] at routing
    intro i
    fin_cases i <;> simp [wordMemoryPortCells,mode,importedConstraintsMemoryPorts,
      MemoryAddress.code,pairCode,Cell.addressCode,routing.secondSpace,routing.thirdSpace,
      canonical,oneVal,wordMemoryAddressWord,rs1,rs2,lo,hi,memLo,memHi]

/-- Actual RAM-only SW routing excludes every native ROM-prefix word cell.
    This is address nonoverlap, not a supplied Sail code frame. -/
theorem store_excludes_rom_cell {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (store : entry.data.family = true)
    (address : BitVec 32) (inside : address.toNat < 4194304) :
    importedConstraintsMemoryPorts[2].address.code w ≠ (Cell.ram address).addressCode := by
  have decoded := NativeWordMemoryDecoderProofs.decoded_fields fields query
  have mask : w 12 = (wordMemoryMask true : ZMod mersenne31Modulus) := by simpa [store] using decoded.mask
  have region := NativeWordMemoryShapeProofs.store_address holds mask
  have actual := addresses holds fields query 2
  have cell : importedConstraintsMemoryPorts[2].address.code w =
      (Cell.ram (wordMemoryAddressWord w).toBitVec).addressCode := by
    simpa [wordMemoryPortCells,store] using actual
  intro equal
  have same := Trace.Proofs.cell_address_injective (cell.symm.trans equal)
  have bits : (wordMemoryAddressWord w).toBitVec = address := by simpa only [Cell.ram.injEq] using same
  have natural := congrArg BitVec.toNat bits
  rw [Word.toBitVec_toNat region.1] at natural
  have lower := region.2.1
  omega

end Airbender.ReducedMachine.NativeWordMemoryPortProofs
