import Airbender.Review.Compiler.NativeSubwordSetup
import Airbender.Proofs.GKRProtocol.ProgramSetupNative

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

/-- Both native cache modes use the public subword prefix and decoder bounds. -/
theorem subword_geometry :
    layouts .subwordMemoryUncached = some {
      «width» := 9, tagged := true, decoderStart := 13238273,
      decoderWords := 1048576, romStart := none, romWords := 0 } ∧
    layouts .subwordMemoryCached = layouts .subwordMemoryUncached := by
  exact ⟨rfl, rfl⟩

/-- The dummy helper row has no program-dependent field. -/
theorem subword_zero_row (wordAt : Nat → BitVec 32) :
    Verification.subwordNativeRow wordAt 0 = Vector.replicate 9 0 := by
  simp [Verification.subwordNativeRow, Verification.subwordZeroDataRegion,
    Verification.subwordZeroData, Setup.Column.get?, Setup.getFromBlocks,
    Setup.Block.length, Setup.Block.get?]
  decide +kernel

/-- Every non-decoder query uses the public fixed or program ROM prefix. -/
theorem subword_query_member (decoder : List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (index : Nat) (query : List Source.BaseField)
    (same : query = subwordRows decoder wordAt index)
    (notDecoder : query.getLast?.getD 0 ≠ 46) :
    ∃ row : Fin 13238273, query =
      ((Verification.subwordNativeRow wordAt row).map
        (fun value : Nat => (value : Source.BaseField))).toList := by
  unfold subwordRows at same
  split at same
  next bounded => exact ⟨⟨index, bounded⟩, same⟩
  next outside =>
    split at same
    next decoderRegion =>
      apply False.elim
      apply notDecoder
      simp [same, ProgramSetup.packTagged]
    next padding =>
      refine ⟨0, ?_⟩
      rw [subword_zero_row]
      simpa using same

/-- Range and timestamp groups keep their exact native interpretation. -/
theorem program_rows_fixed_group
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (configuration : Configuration)
    (group : Fin 3) (index : Nat) (other : group.val ≠ 0) :
    programRows decoder wordAt configuration group index = retainedRows configuration group index := by
  cases configuration <;>
    simp only [programRows, if_neg other, rows_fixed_group decoder wordAt _ group index other]

end Airbender.Compiler.NativeProgramSetup
