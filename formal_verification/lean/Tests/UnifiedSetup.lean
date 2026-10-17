import Airbender.Proofs.UnifiedReduced.BinaryLookups
import Airbender.Proofs.UnifiedReduced.ShiftLookups
import Airbender.Proofs.BabyBear

namespace Tests.UnifiedSetup
open Airbender UnifiedReduced Arithmetic Verification
set_option warningAsError true

private def query (output : Nat) : Vector (Expression (ZMod babyBearModulus)) 10 :=
  #v[.const 0xac, .const 0x39, .const (output : ZMod babyBearModulus),
    .const 0, .const 0, .const 0, .const 0, .const 0, .const 0, .const 52]

private def environment : Environment (ZMod babyBearModulus) := Verification.environment (fun _ => 0)

theorem wide_xor_accepted : (Lookup.mk (Setup.table default).toRaw (query 0x95)).Contains environment := by
  change ∃ i : Fin 2097537, (query 0x95).map (Expression.eval environment) =
    (Setup.row default i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨⟨257 + 0xac * 256 + 0x39, by decide⟩, ?_⟩
  rw [Setup.Proofs.row_eq_reference]
  simp only [Setup.referenceRow, Setup.referenceFixedRow, Setup.referenceBinaryRow,
    Verification.shiftBinopRow_eq_reference]; decide +kernel

theorem wide_xor_checked :
    BitVec.ofNat 8 ((query 0x95)[2].eval environment).val =
      byteOperation 4 (BitVec.ofNat 8 ((query 0x95)[0].eval environment).val)
        (BitVec.ofNat 8 ((query 0x95)[1].eval environment).val) :=
  (Setup.Proofs.wide_lookup (by decide) wide_xor_accepted 4 (Or.inl rfl) (by decide)).2.2.2.1

theorem wrong_result_rejected :
    ¬ (Lookup.mk (Setup.table default).toRaw (query 0x94)).Contains environment := by
  intro accepted
  have result := (Setup.Proofs.wide_lookup (by decide) accepted 4 (Or.inl rfl) (by decide)).2.2.2.1
  exact (by decide : BitVec.ofNat 8 0x94 ≠ byteOperation 4 (BitVec.ofNat 8 0xac) (BitVec.ofNat 8 0x39)) result

theorem native_zero_row : Setup.row default ⟨0, by decide⟩ = Vector.replicate 10 0 := by decide +kernel

end Tests.UnifiedSetup
