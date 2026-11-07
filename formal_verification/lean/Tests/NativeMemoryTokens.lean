import Airbender.Review.Circuits.ReducedMachine.MemoryTokenTheorems

namespace Airbender.Tests.NativeMemoryTokens
open Airbender.NativeMemoryTokens Airbender.NativeMemoryTokenProofs
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private def wideKey : MemoryKey := ⟨⟨2,65536,65537⟩,#v[2147483646,65536],#v[600000,700000]⟩
private def lowKey : MemoryKey := ⟨⟨0,65536,0⟩,#v[0,0],#v[0,0]⟩
private def highKey : MemoryKey := ⟨⟨0,0,1⟩,#v[0,0],#v[0,0]⟩
private def zeroChallenges : MemoryKeyChallenges (ZMod mersenne31Modulus) := ⟨0,0,0,0,0,0,0⟩

/-- Field complement precedes Nat coding; Nat subtraction would erase this raw
    nonboolean indicator. This is a reference key, not an accepted circuit row. -/
theorem raw_indicator_complement :
    (Nat.unpair (encodeKey wideKey).address).1 = 2147483646 := by decide +kernel

/-- An arbitrary Clean Nat token can be outside the encoded field-key image;
    the bridge makes only the proved left-inverse claim on actual native keys. -/
theorem arbitrary_nat_token_not_roundtrip :
    let token : Trace.MemoryToken mersenne31Modulus := ⟨Nat.pair 2147483647 0,(0,0),0⟩
    encodeKey (decodeKey token) ≠ token := by decide +kernel

theorem wide_field_roundtrip : decodeKey (encodeKey wideKey) = wideKey := decode_encode _

theorem full_wide_limbs : (decodeKey (encodeKey wideKey)).value = #v[2147483646,65536] ∧
    (decodeKey (encodeKey wideKey)).time = #v[600000,700000] := by
  rw [decode_encode]
  exact ⟨rfl,rfl⟩

/-- Numeric radix packing can alias unranged field limbs; the token bridge keeps
    the pair distinct rather than assuming initialized16-bit bounds. -/
theorem radix_alias_tokens_distinct :
    (65536 : Nat)+65536*0 = 0+65536*1 ∧ encodeKey lowKey ≠ encodeKey highKey := by
  constructor
  · decide
  · intro equal
    have same := encode_injective equal
    have low := congrArg (fun key : MemoryKey => key.address.low) same
    change (65536 : ZMod mersenne31Modulus) = 0 at low
    exact (by decide : (65536 : ZMod mersenne31Modulus) ≠ 0) low

theorem mixed_polarity_preserves_raw (w : Nat → ZMod mersenne31Modulus) (selector : Nat)
    (columns : Vector Nat 2) :
    encodeAddress (nativeAddress w (.mixed selector false columns)) =
      Trace.MemoryAddress.code (.mixed selector false columns) w := mixed_address w selector false columns

theorem actual_main_both_sides (w : Nat → ZMod mersenne31Modulus) :
    ((List.finRange 3).map fun slot => encodeKey (mainMemoryKey w slot false)) = mainTokens w false ∧
    ((List.finRange 3).map fun slot => encodeKey (mainMemoryKey w slot true)) = mainTokens w true :=
  ⟨actual_main_memory_tokens w false,actual_main_memory_tokens w true⟩

private def clockWitness (i : Nat) : ZMod mersenne31Modulus := if i = 2 then 4 else 0

theorem readonly_refresh_not_erased :
    (encodeKey (mainMemoryKey clockWitness 0 false)).value =
      (encodeKey (mainMemoryKey clockWitness 0 true)).value ∧
    (encodeKey (mainMemoryKey clockWitness 0 false)).time ≠
      (encodeKey (mainMemoryKey clockWitness 0 true)).time := by decide +kernel

private def thirdWitness (i : Nat) : ZMod mersenne31Modulus :=
  if i = 41 then 9 else if i = 42 then 10 else if i = 43 then 11 else if i = 44 then 12 else 0

theorem third_oldread_and_unmasked_write :
    (encodeKey (mainMemoryKey thirdWitness 2 false)).value = Nat.pair 9 10 ∧
    (encodeKey (mainMemoryKey thirdWitness 2 true)).value = Nat.pair 11 12 ∧
    (Nat.unpair (encodeKey (mainMemoryKey thirdWitness 2 true)).address).1 = 1 := by decide +kernel

theorem all_worker_keys (w : Nat → ZMod mersenne31Modulus) (write : Bool) :
    (workerTokens w write).map decodeKey = (List.finRange 43).map (fun slot => quotientMemoryKey w slot write) :=
  worker_keys w write

/-- Even the zero body observation has43 slots on each side; no inactive-row
    token filter, accepted witness or zero-clock exclusion is asserted. -/
theorem inactive_tokens_retained :
    (workerTokens (fun _ => 0) false).length = 43 ∧ (workerTokens (fun _ => 0) true).length = 43 :=
  ⟨worker_count _ false,worker_count _ true⟩

theorem public_all_register_initials (index : Fin 32) :
    (encodeKey (registerInitialKey index)).address = Nat.pair 0 (Nat.pair index.val 0) ∧
    (encodeKey (registerInitialKey index)).time = (0,0) := by
  have bound : index.val < mersenne31Modulus := lt_trans index.isLt (by decide)
  simp [encodeKey,encodeAddress,registerInitialKey,ZMod.val_natCast_of_lt bound]

theorem public_x0_time_retained (inputs : PublicBoundary) :
    (encodeKey (registerFinalKey inputs 0)).time = ((inputs.registers 0).time[0],(inputs.registers 0).time[1]) := rfl

theorem duplicate_multiplicity_retained :
    ¬ ([lowKey,lowKey].map encodeKey).Perm ([lowKey].map encodeKey) := by
  intro equal
  have size := equal.length_eq
  change 2 = 1 at size
  omega

theorem scalar_collision_is_not_token_identity :
    tokenArgument (RingHom.id (ZMod mersenne31Modulus)) zeroChallenges (encodeKey lowKey) =
      tokenArgument (RingHom.id (ZMod mersenne31Modulus)) zeroChallenges (encodeKey highKey) ∧
    encodeKey lowKey ≠ encodeKey highKey := by
  constructor
  · rw [argument_encoding,argument_encoding]
    simp [memoryKeyArgument,zeroChallenges,lowKey,highKey]
  · exact radix_alias_tokens_distinct.2

theorem complete_main_factor_transport {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) (w : Nat → ZMod mersenne31Modulus) (write : Bool) :
    ((mainTokens w write).map (tokenArgument embed ch)).prod = mainMemoryProduct embed ch w write :=
  main_product embed ch w write

theorem complete_worker_factor_transport {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) (w : Nat → ZMod mersenne31Modulus) (write : Bool) :
    ((workerTokens w write).map (tokenArgument embed ch)).prod = memoryKeyProduct embed ch w write :=
  worker_product embed ch w write

end Airbender.Tests.NativeMemoryTokens
