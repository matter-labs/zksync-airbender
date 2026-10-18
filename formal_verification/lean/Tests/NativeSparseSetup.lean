import Airbender.Review.Trace.Families.WordMemory.SparseDecoder

namespace Tests.NativeSparseSetup
open Airbender Trace Setup WordMemory NativeSparse

/-- Exact original public bytes underlie the complete sparse table certificate. -/
theorem constructed : sparseDecoderSetupImage before 4 20 = some setup :=
  WordMemory.Proofs.sparse_fixture_image

theorem supported_after_hole :
    holesDecoder.rowNat ⟨1, by decide⟩ = Vector.replicate 10 2147483646 ∧
    holesDecoder.rowNat ⟨2, by decide⟩ = #v[8,0,1,3,0,1,16,0,2,1] ∧
    holesDecoder.rowNat ⟨3, by decide⟩ = #v[12,0,1,0,0,1,16,0,2,0] := by decide +kernel

theorem original_sources :
    storeEntry.SourceWith before decoderFields ∧ x0Entry.SourceWith before decoderFields := by
  constructor <;> apply (Trace.Proofs.sparse_setup_sources constructed ?_).1
  all_goals simp [SparseDecoderSetup.program, setup]

private def missingBefore : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with mem := Std.ExtHashMap.emptyWithCapacity }

/-- Every supplied word must be readable, even if it would become a hole. -/
theorem missing_hole_bytes : sparseDecoderSetupImage missingBefore 1 20 = none := by
  simp [sparseDecoderSetupImage, sparseDecoderSetupImageWith, programSlotWith, Cell.read,
    _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte, EStateM.run, get,
    getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw, missingBefore]

theorem insufficient_capacity : sparseDecoderSetupImage before 4 1 = none := rfl

theorem inputs_retained :
    (List.range 4).map holesText.get? =
      [some 0x0100a183, some 0xc0001073, some 0x0030a823, some 0x0100a003] := by decide +kernel

end Tests.NativeSparseSetup
