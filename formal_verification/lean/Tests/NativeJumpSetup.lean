import Tests.JumpDecoder
import Lean.Elab.GuardMsgs

namespace Tests.NativeJumpSetup
open Airbender Trace Setup JumpBranchSlt NativeSetup

/-- The public text and native rows are independently read and decoded. -/
theorem constructed : sparseDecoderSetupImage before 3 20 = some setup :=
  Proofs.native_fixture_image

theorem public_text : controlTextWords = 3 ∧
    (List.range 3).map controlText.get? = words.toList.map (some ∘ BitVec.toNat) := by
  decide +kernel

theorem signed_jal : controlDecoder.rowNat ⟨0, by decide⟩ =
    #v[0,0,0,0,1,0,65532,65535,7,1] := by decide +kernel

/-- The unsupported PC 4 slot is retained; the later original x0 instruction
    keeps its native SLTI mask, source index and independent zero flag. -/
theorem post_hole_x0 : controlDecoder.rowNat ⟨2, by decide⟩ =
    #v[8,0,1,0,0,1,65535,65535,3,8] ∧ sltiEntry.instruction =
      .ITYPE (4095, .Regidx 1, .Regidx 0, .SLTIU) := by
  exact ⟨by decide +kernel, rfl⟩

theorem hole_and_tail :
    controlDecoder.rowNat ⟨1, by decide⟩ = Vector.replicate 10 2147483646 ∧
    controlDecoder.rowNat ⟨1048575, by decide⟩ = Vector.replicate 10 2147483646 := by
  decide +kernel

theorem exported_jal : Fetched Tests.JumpDecoder.assignment before ∧
    (Tests.JumpDecoder.assignment 13).val < 65536 ∧
    (Tests.JumpDecoder.assignment 14).val < 65536 :=
  exported_decoder_soundness Tests.JumpDecoder.native_constraints
    ⟨⟨0, by decide⟩, by decide +kernel⟩

/-- Reusing the earlier local tag-zero witness fails actual exported membership. -/
theorem wrong_tag_rejected : ¬∃ i : Fin 1048576,
    decoderQuery Tests.JumpPC.negativeJal = controlDecoder.row i := by
  rintro ⟨i, same⟩
  exact Tests.JumpDecoder.wrong_jal_tag_rejected
    ⟨i, same.trans (Proofs.native_exported_rows i)⟩

/-- error: native decoder import failed: unsupported native decoder profile -/
#guard_msgs in
import_native_decoder wrong from "artifacts/setup/jump-decoder-native.json"

/-- error: native decoder import failed: unsupported native decoder profile -/
#guard_msgs in
import_native_control_decoder wrong from "artifacts/setup/arithmetic-native.json"

end Tests.NativeJumpSetup
