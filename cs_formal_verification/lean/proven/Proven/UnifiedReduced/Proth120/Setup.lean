module
public import Human.Circuits.UnifiedReduced.Tables.Proth120
public import Proven.UnifiedReduced.Proth120.Standard.Artifact

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Verification

/-- Native tag 34 covers the wrap ROM. The decoder occupies one row per ROM word.
    The logical membership table below enumerates the same number of non-decoder rows. -/
theorem setup_geometry :
    importedConstraintsLayoutSource.table_offsets[35].val - importedConstraintsLayoutSource.table_offsets[34].val = 2 ^ 17 ∧
    importedConstraintsLayoutSource.offset_for_decoder_table = 1180033 ∧
    importedConstraintsLayoutSource.total_tables_size - importedConstraintsLayoutSource.offset_for_decoder_table = 2 ^ 17 := by
  decide +kernel

private theorem query_in_full_setup {words : Nat → BitVec 32} {env : Environment (ZMod proth120Modulus)}
    {entry : Vector (Expression (ZMod proth120Modulus)) 10}
    (h : (Lookup.mk (tableWith words).toRaw entry).Contains env) :
    (Lookup.mk (Setup.tableWith words).toRaw entry).Contains env := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i, lt_of_lt_of_le i.isLt (by decide : 1180033 ≤ 2097537)⟩, hi⟩

/-- Every wrap setup row is also present in the ordinary modeled unified table, at the same index.
    The 120 equations and all scalar ranges are independent of the pooled lookup table. -/
theorem full_setup_holds {words : Nat → BitVec 32} {env : Environment (ZMod proth120Modulus)}
    (h : FlatOperation.ConstraintsHoldFlat env (importedConstraints (tableWith words))) :
    FlatOperation.ConstraintsHoldFlat env (Standard.importedConstraints (Setup.tableWith words)) := by
  apply Standard.holds
  let src := importedConstraints (tableWith words)
  let dst := importedConstraints (Setup.tableWith (p := proth120Modulus) words)
  change FlatOperation.ConstraintsHoldFlat env dst
  rw [← List.take_append_drop 135 dst]
  apply holds_append
  · exact holds_of_sublist h (show (dst.take 135).Sublist src from List.take_sublist 135 src)
  · obtain ⟨a,b,c,d,e,_⟩ := holds_of_sublist h (List.drop_sublist 135 src)
    exact ⟨query_in_full_setup a, query_in_full_setup b, query_in_full_setup c,
      query_in_full_setup d, query_in_full_setup e, trivial⟩

end Airbender.UnifiedReduced.Proth120
