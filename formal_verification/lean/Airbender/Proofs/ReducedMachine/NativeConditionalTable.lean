import Airbender.Review.Circuits.ReducedMachine.Comparison
import Airbender.Proofs.ReducedMachine.NativePool

namespace Airbender.ReducedMachine.NativeConditionalTableProofs
open Native NativeFixed Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Every row of the actual tag22 region, including all inconsistent flag combinations. -/
theorem rows : ∀ i : Fin 128, dataT22.rowNat i = conditionalRow i := by
  decide +kernel

/-- Full native pool membership derives a canonical key and both actual outputs. -/
theorem result (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (tag : query[3] = 22) :
    ∃ i : Fin 128, query = (conditionalRow i).map Nat.cast := by
  obtain ⟨i,same⟩ := NativePoolProofs.selected_region query member .conditional tag
  change query = dataT22.row i at same
  exact ⟨i,by simpa only [Setup.TableData.row,rows] using same⟩

/-- The native comparison forms cannot jump, and their candidate is the exact
    signed/unsigned flag resolution at the derived canonical packed key. -/
theorem comparison {key jump value : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,jump,value,22])
    (selected : key.val % 8 = 2 ∨ key.val % 8 = 3) :
    key.val < 128 ∧ jump = 0 ∧
      value = if conditionalFlag (key.val / 8) (key.val % 8) then 1 else 0 := by
  obtain ⟨i,same⟩ := result _ member rfl
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [conditionalRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[0]) same
  have canonical : key.val = i.val := by
    rw [head,ZMod.val_natCast_of_lt (lt_trans i.isLt (by decide))]
  have mode : i.val % 8 = 2 ∨ i.val % 8 = 3 := by simpa only [canonical] using selected
  have j := congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[1]) same
  have v := congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[2]) same
  refine ⟨by rw [canonical]; exact i.isLt,?_,?_⟩
  · simpa [conditionalRow,mode] using j
  · rw [canonical]
    simpa [conditionalRow,mode] using v

end Airbender.ReducedMachine.NativeConditionalTableProofs
