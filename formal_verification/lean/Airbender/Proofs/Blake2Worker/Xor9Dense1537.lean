import Mathlib.Tactic.FinCases
import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates
namespace Airbender.Blake2Worker.Xor9Dense1537
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem length : dataT29Column2Block1537.length = 512 := by
  simp only [dataT29Column2Block1537,Block.length,raw_size_append,raw_literal_size]
  rfl


private theorem windows (high : Fin 32) (low : Fin 16) :
    dataT29Column2Block1537.get? (high.val*16+low.val) =
    some ((174592+(high.val*16+low.val))/512 ^^^ (174592+(high.val*16+low.val))%512) := by
  have bound : high.val*16+low.val < 512 := by omega
  unfold Block.get?
  rw [length,if_pos bound]
  simp only [dataT29Column2Block1537]
  simp only [raw_get_append,raw_size_append,raw_literal_size]
  fin_cases high <;> fin_cases low <;> decide +kernel

theorem reads (i : Fin 512) : dataT29Column2Block1537.get? i.val =
    some ((174592+i.val)/512 ^^^ (174592+i.val)%512) := by
  have result := windows ⟨i.val/16,by have := i.isLt; omega⟩ ⟨i.val%16,Nat.mod_lt _ (by decide)⟩
  have same : i.val/16*16+i.val%16 = i.val := by omega
  simpa only [same] using result

end Airbender.Blake2Worker.Xor9Dense1537
