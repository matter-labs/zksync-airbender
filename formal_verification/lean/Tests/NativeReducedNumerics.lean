import Airbender.Review.Circuits.ReducedMachine.Theorems

namespace Tests.NativeReducedNumerics
open Airbender Airbender.ReducedMachine Airbender.Verification

-- Lift independently certified actual rows at the native region offset.
private theorem at_shift (n : Nat) (bound : n < 4194304) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      ((#v[n,(NativeFixed.shiftOutputs n)[0],(NativeFixed.shiftOutputs n)[1],37]).map
        (Nat.cast : Nat → ZMod mersenne31Modulus)) := by
  refine ⟨⟨n + 1511681,by change n + 1511681 < 5771521; omega⟩,?_⟩
  change _ = (NativeFixed.rowNat ⟨n + 1511681,_⟩).map Nat.cast
  have h0 : ¬ n + 1511681 < 1 := by omega
  have h1 : ¬ n + 1511681 < 65537 := by omega
  have h2 : ¬ n + 1511681 < 131073 := by omega
  have h3 : ¬ n + 1511681 < 196609 := by omega
  have h4 : ¬ n + 1511681 < 262145 := by omega
  have h5 : ¬ n + 1511681 < 327681 := by omega
  have h6 : ¬ n + 1511681 < 393217 := by omega
  have h7 : ¬ n + 1511681 < 393345 := by omega
  have h8 : ¬ n + 1511681 < 393473 := by omega
  have h9 : ¬ n + 1511681 < 459009 := by omega
  have h10 : ¬ n + 1511681 < 1507585 := by omega
  have h11 : ¬ n + 1511681 < 1511681 := by omega
  have selected : n + 1511681 < 5705985 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,dif_neg h6,dif_neg h7,dif_neg h8,dif_neg h9,dif_neg h10,dif_neg h11,dif_pos selected]
  simp only [Nat.add_sub_cancel_right]
  rw [NativeShiftRowProofs.rows]

theorem left_first :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,37] := by
  convert at_shift 0 (by decide) using 1
  decide +kernel

theorem left_last :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[2097151,0,32768,37] := by
  convert at_shift 2097151 (by decide) using 1
  decide +kernel

theorem right_first :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[2097152,0,0,37] := by
  convert at_shift 2097152 (by decide) using 1
  decide +kernel

theorem right_zero_shift :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[2162687,65535,0,37] := by
  convert at_shift 2162687 (by decide) using 1
  decide +kernel

theorem right_cross_bit :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[2195457,16384,32768,37] := by
  convert at_shift 2195457 (by decide) using 1
  decide +kernel

theorem right_shift16 :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[3211263,0,65535,37] := by
  convert at_shift 3211263 (by decide) using 1
  decide +kernel

theorem right_last :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[4194303,0,1,37] := by
  convert at_shift 4194303 (by decide) using 1
  decide +kernel

theorem reversed_right_outputs_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[2195457,32768,16384,37] := by
  intro member
  have result := (NativeFixed.shift_implementation _ member rfl).2.1
  exact (by decide +kernel : ¬ (32768 : ZMod mersenne31Modulus).val =
    (NativeFixed.shiftOutputs (2195457 : ZMod mersenne31Modulus).val)[0]) result

theorem corrupted_left_carry_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[2097151,0,32767,37] := by
  intro member
  have result := (NativeFixed.shift_implementation _ member rfl).2.2.1
  exact (by decide +kernel : ¬ (32767 : ZMod mersenne31Modulus).val =
    (NativeFixed.shiftOutputs (2097151 : ZMod mersenne31Modulus).val)[1]) result

theorem outside_key_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[4194304,0,0,37] := by
  intro member
  have bound := (NativeFixed.shift_implementation _ member rfl).1
  exact (by decide +kernel : ¬ (4194304 : ZMod mersenne31Modulus).val < 4194304) bound

/-- Even discarded native writes retain the numerical contribution obligations. -/
theorem discarded_contributions_bounded {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (Native.importedConstraints NativeFixed.table))
    (mode : Native.ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus))
    (discarded : Native.rdZeroFlag w = 1) :
    Native.rdWrite w = #v[0,0] ∧
      (Native.shiftLowParts w)[0].val < 65536 ∧ (Native.shiftLowParts w)[1].val < 65536 ∧
      (Native.shiftHighParts w)[0].val < 65536 ∧ (Native.shiftHighParts w)[1].val < 65536 := by
  have write := (Native.shift_masked_write holds mode useRegister mask).2
  have low := (Native.shift_contribution_values holds mode useRegister mask ⟨0,by decide⟩).2.2.2
  have high := (Native.shift_contribution_values holds mode useRegister mask ⟨1,by decide⟩).2.2.2
  refine ⟨?_,low.1,low.2,high.1,high.2⟩
  have zeros (v : Vector (ZMod mersenne31Modulus) 2) :
      v.map (fun _ => (0 : ZMod mersenne31Modulus)) = #v[0,0] := by
    ext lane bound
    interval_cases lane <;> simp
  rw [discarded] at write
  simp only [sub_self,zero_mul] at write
  exact write.trans (zeros _)

end Tests.NativeReducedNumerics
