import GKRProtocol.MaterializedRanges
import Airbender.Review.Helpers.Context.Timestamps

namespace Airbender.Compiler
set_option warningAsError true

/-- The retained scalar Clean table is inhabited by each bounded residue of its
actual literal affine prefix, independently of prover-supplied table arrays. -/
theorem scalar_clean_contains (data : Setup.TableData 1) (name : String) (limit : Nat)
    (offset : data.offset = 0) (rest : List Setup.Block)
    (initialBlocks : (data.columns[0]).blocks.toList = .affine limit 0 1 :: rest)
    (domain : limit ≤ data.length) (value : Source.BaseField) (bounded : value.val < limit)
    (provided : Array Source.BaseField) :
    (data.scalarTable (p := babyBearModulus) name).Contains provided value := by
  let index : Fin data.length := ⟨value.val, lt_of_lt_of_le bounded domain⟩
  change ∃ row : Fin data.length, value = ((data.row row)[0] : Source.BaseField)
  refine ⟨index, ?_⟩
  rw [scalar_row_affine_prefix data limit offset rest initialBlocks index bounded]
  exact (ZMod.natCast_zmod_val value).symm

private theorem range16_prefix : Verification.importedRange16.columns[0].blocks.toList =
    Setup.Block.affine 65536 0 1 :: Verification.importedRange16.columns[0].blocks.toList.tail := by decide +kernel

private theorem timestamp_prefix : Verification.importedTimestamp19.columns[0].blocks.toList =
    Setup.Block.affine 524288 0 1 :: Verification.importedTimestamp19.columns[0].blocks.toList.tail := by decide +kernel

theorem range16_clean_contains (value : Source.BaseField) (bounded : value.val < 65536)
    (provided : Array Source.BaseField) :
    (Verification.range16Table (p := babyBearModulus)).Contains provided value :=
  scalar_clean_contains Verification.importedRange16 "Airbender.Range16" 65536 rfl
    (Verification.importedRange16.columns[0]).blocks.toList.tail range16_prefix (by decide +kernel)
    value bounded provided

theorem timestamp_clean_contains (value : Source.BaseField) (bounded : value.val < 524288)
    (provided : Array Source.BaseField) :
    (Trace.timestampTable (p := babyBearModulus)).Contains provided value :=
  scalar_clean_contains Verification.importedTimestamp19 "Airbender.Timestamp19" 524288 rfl
    (Verification.importedTimestamp19.columns[0]).blocks.toList.tail timestamp_prefix (by decide +kernel)
    value bounded provided

end Airbender.Compiler
