import Airbender.Proofs.BabyBear
import Airbender.Proofs.Tables.Decoder.AddSub
import Airbender.Proofs.Tables.ImportedROMReads
import Airbender.Proofs.Trace.Program

namespace Airbender.Tests.NativeSetupSemantics
open Trace Trace.NativeDecoder Trace.NativeDecoder.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

/-- A real imported decoder row admits its actual decoded instruction. -/
theorem accepted_decoder :
    addSubSetup.lookup ((pooledEntry 0).query (p := babyBearModulus)) := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  decide +kernel

/-- A real native ROM query retrieves the first independently imported word. -/
theorem accepted_rom :
    (ROM.importedTable (p := babyBearModulus)).Contains #[]
      #v[0, 19, 0, 0, 0, 0, 0, 0, 34] := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  decide +kernel

/-- Disabled native lookups retain the actual zero entry. -/
theorem accepted_disabled :
    (ROM.importedTable (p := babyBearModulus)).Contains #[]
      (Vector.replicate 9 0) := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  decide +kernel

private def absentQuery : Vector (ZMod babyBearModulus) 9 := #v[16, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The imported complete domain cannot manufacture an instruction at an
    unsupported program slot from a fixed-table prefix or committed filler. -/
theorem unsupported_decoder_rejected : ¬ addSubSetup.lookup absentQuery := by
  intro accepted
  have semantic := AddSub.lookup_sound (by decide) absentQuery (by decide) accepted
  obtain ⟨entry, member, family, equal⟩ := Trace.Proofs.decoder_member semantic
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  have component := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[0]) equal
  fin_cases index <;> revert component <;> decide +kernel

end Airbender.Tests.NativeSetupSemantics
