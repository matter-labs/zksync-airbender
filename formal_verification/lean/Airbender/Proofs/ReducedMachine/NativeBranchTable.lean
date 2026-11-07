import Airbender.Proofs.ReducedMachine.NativeConditionalTable

namespace Airbender.ReducedMachine.NativeBranchTableProofs
open Native NativeFixed Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual branch tags select the jump output, leaving comparison output zero.
    The complete native resolver certificate is reused without a split identity. -/
theorem branch {key jump value : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,jump,value,22])
    (selected : key.val % 8 ∈ [0,1,4,5,6,7]) :
    key.val < 128 ∧ value = 0 ∧
      jump = if conditionalFlag (key.val / 8) (key.val % 8) then 1 else 0 := by
  obtain ⟨i,same⟩ := NativeConditionalTableProofs.result _ member rfl
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [conditionalRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[0]) same
  have canonical : key.val = i.val := by
    rw [head,ZMod.val_natCast_of_lt (lt_trans i.isLt (by decide))]
  have mode : i.val % 8 ≠ 2 ∧ i.val % 8 ≠ 3 := by
    rw [canonical] at selected
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at selected
    omega
  have j := congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[1]) same
  have v := congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[2]) same
  refine ⟨by rw [canonical]; exact i.isLt,?_,?_⟩
  · simpa [conditionalRow,mode.1,mode.2] using v
  · rw [canonical]
    simpa [conditionalRow,mode.1,mode.2] using j

end Airbender.ReducedMachine.NativeBranchTableProofs
