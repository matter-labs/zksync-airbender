import Airbender.Review.Circuits.ReducedMachine.Theorems
import Airbender.Proofs.ReducedMachine.NativeArtifactChecks

namespace Tests.NativeReducedPool
open Airbender Airbender.ReducedMachine

private theorem at_sign (n : Nat) (bound : n < 65536) :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[]
      ((#v[n,n / 32768,n / 256,16]).map (Nat.cast : Nat → ZMod mersenne31Modulus)) := by
  refine ⟨⟨n + 196609,by change n + 196609 < 5771521; omega⟩,?_⟩
  change _ = (NativeFixed.rowNat ⟨n + 196609,_⟩).map Nat.cast
  have h0 : ¬ n + 196609 < 1 := by omega
  have h1 : ¬ n + 196609 < 65537 := by omega
  have h2 : ¬ n + 196609 < 131073 := by omega
  have h3 : ¬ n + 196609 < 196609 := by omega
  have sign : n + 196609 < 262145 := by omega
  rw [NativeFixed.rowNat,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_pos sign]
  simp only [Nat.add_sub_cancel_right]
  change _ = (SignHigh.data.rowNat ⟨n,bound⟩).map Nat.cast
  rw [SignHighProofs.rows]

theorem native_geometry : Native.importedConstraintsSetupColumns.genericRows = 5771521 ∧
    NativeFixed.dataT47.nativeOffset = 5705985 ∧ NativeFixed.dataT47.length = 65536 :=
  ⟨rfl,rfl,rfl⟩

theorem retained_public_inputs : NativeFixed.dataImageWords = 8 ∧
    NativeFixed.dataDelegationCSRs = #[1988,1989] ∧ NativeFixed.dataAllowNonDeterminism = true :=
  ⟨rfl,rfl,rfl⟩

theorem zero_member : (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,0] := by
  refine ⟨⟨0,by decide⟩,?_⟩
  decide +kernel

theorem truncation_last :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[65535,31,0,47] := by
  refine ⟨⟨5771520,by decide⟩,?_⟩
  decide +kernel

theorem negative_sign_member :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[32768,1,128,16] := by
  convert at_sign 32768 (by decide) using 1; decide +kernel

theorem last_sign_member :
    (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[65535,1,255,16] := by
  convert at_sign 65535 (by decide) using 1; decide +kernel

theorem bad_sign_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[32768,0,128,16] := by
  intro member
  have result := (NativeFixed.sign_high _ member rfl).2.1
  exact (by decide +kernel : ¬ (0 : ZMod mersenne31Modulus).val =
    (32768 : ZMod mersenne31Modulus).val / 32768) result

theorem bad_high_rejected :
    ¬ (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[65535,1,254,16] := by
  intro member
  have result := (NativeFixed.sign_high _ member rfl).2.2.1
  exact (by decide +kernel : ¬ (254 : ZMod mersenne31Modulus).val =
    (65535 : ZMod mersenne31Modulus).val / 256) result

end Tests.NativeReducedPool
