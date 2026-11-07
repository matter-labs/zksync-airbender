import Airbender.Proofs.ReducedMachine.NativeWordMemoryTables

namespace Airbender.ReducedMachine.NativeWordMemoryTableValues
open NativeFixed Setup Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem offset {key first second : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,first,second,18]) :
    key.val < 65536 ∧ first = ((key.val%2) : Nat) ∧ second = ((key.val/2%2) : Nat) := by
  obtain ⟨i,same⟩ := NativePoolProofs.selected_region _ member .memoryOffset rfl
  change #v[key,first,second,18] = dataT18.row i at same
  have actual : #v[key,first,second,18] = (wordOffsetRow i.val).map Nat.cast := by
    simpa only [TableData.row,NativeWordMemoryTableProofs.offset_rows] using same
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [wordOffsetRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[0]) actual
  have canonical : key.val = i.val := by
    rw [head,ZMod.val_natCast_of_lt (lt_trans i.isLt (by decide))]
  refine ⟨by rw [canonical]; exact i.isLt,?_,?_⟩
  · rw [canonical]
    simpa [wordOffsetRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[1]) actual
  · rw [canonical]
    simpa [wordOffsetRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[2]) actual

theorem separator {key first second : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,first,second,23]) :
    key.val < 65536 ∧ first = ((if key.val < 64 then 0 else 1) : Nat) ∧ second = ((key.val%64) : Nat) := by
  obtain ⟨i,same⟩ := NativePoolProofs.selected_region _ member .separator rfl
  change #v[key,first,second,23] = dataT23.row i at same
  have actual : #v[key,first,second,23] = (wordSeparatorRow i.val).map Nat.cast := by
    simpa only [TableData.row,NativeWordMemoryTableProofs.separator_rows] using same
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [wordSeparatorRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[0]) actual
  have canonical : key.val = i.val := by
    rw [head,ZMod.val_natCast_of_lt (lt_trans i.isLt (by decide))]
  refine ⟨by rw [canonical]; exact i.isLt,?_,?_⟩
  · rw [canonical]
    simpa [wordSeparatorRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[1]) actual
  · rw [canonical]
    simpa [wordSeparatorRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[2]) actual

theorem rom {key lo hi : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,lo,hi,24]) :
    key.val < 4194304 ∧ key.val % 4 = 0 ∧
      #v[lo,hi] = (wordROMValue (key.val/4)).map Nat.cast := by
  obtain ⟨i,same⟩ := NativePoolProofs.selected_region _ member .rom rfl
  change #v[key,lo,hi,24] = dataT24.row i at same
  have actual : #v[key,lo,hi,24] = (wordROMRow i.val).map Nat.cast := by
    simpa only [TableData.row,NativeWordMemoryTableProofs.rom_rows] using same
  have head : key = (4*i.val : Nat) := by
    simpa [wordROMRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[0]) actual
  have bound : 4*i.val < 4194304 := by have inside : i.val < 1048576 := i.isLt; omega
  have canonical : key.val = 4*i.val := by
    rw [head,ZMod.val_natCast_of_lt (lt_trans bound (by decide))]
  refine ⟨by omega,by omega,?_⟩
  have index : key.val/4 = i.val := by omega
  rw [index]
  have low := congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[1]) actual
  have high := congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[2]) actual
  apply Vector.ext
  intro lane bound
  interval_cases lane
  · simpa [wordROMRow] using low
  · simpa [wordROMRow] using high

theorem rom_value_bounds (index : Nat) :
    (wordROMValue index)[0] < 65536 ∧ (wordROMValue index)[1] < 65536 := by
  unfold wordROMValue
  split <;> norm_num

end Airbender.ReducedMachine.NativeWordMemoryTableValues
