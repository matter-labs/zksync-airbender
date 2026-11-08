module
public import Slop.Trace.RVFamilySelectors
public import Slop.Trace.RVZero
public import Slop.Trace.RVZeroRows
public import Slop.Trace.Pooled

@[expose] public section

/-! The pooled x0 law: each family's row lemma (`RVZeroRows`) assembled over the pooled decoder projection. -/

namespace Airbender.Trace.RVZero
open Arithmetic Trace.Proofs

/-- The RV-route pooled row law: the pooled entry's metadata is `rvPooledDecoderFields` of an `RV.Instr` (the family
    split is `rv_pooled_fields_cases`), and each family's twin discharges its local x0 law. -/
theorem rv_pooled_row_zero_preserving {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (setup : PooledSetup p) (row : Row p PooledFamily)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup))
    {entry : RVPooledProgramEntry} {i : RV.Instr} (fields : rvPooledDecoderFields i = some entry.data)
    (family : entry.data.family = row.family) (query : row.decoderQuery = entry.query) :
    RowZeroPreserving row := by
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨pc, bits, data⟩ := entry
  obtain h | h | h | h | h := rv_pooled_fields_cases fields
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      cases mode : d.family
      all_goals simp only [DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
      all_goals subst kind
      all_goals
        have query' : _ = (⟨pc, bits, d⟩ : RVProgramEntry).query := query
        have mask : d.mask < 512 := by
          have bound := (rvStandardDecoderRules.bounds _ _ fd).2
          omega
      · have fetch : RVFetched (⟨.addSub, w⟩ : Row p) rvDecoderFields :=
          ⟨⟨pc, bits, d⟩, i, fd, mode, query',
            rv_row_query_selectors_of_bound limbField setup.wordMemory constraints mask query'⟩
        exact row_zero_write_from_reads rvStandardDecoderRules hp ⟨.addSub, w⟩ setup.wordMemory constraints fetch
      · have fetch : RVFetched (⟨.wordMemory, w⟩ : Row p) rvDecoderFields :=
          ⟨⟨pc, bits, d⟩, i, fd, mode, query',
            rv_row_query_selectors_of_bound limbField setup.wordMemory constraints mask query'⟩
        exact row_zero_write_from_reads rvStandardDecoderRules hp ⟨.wordMemory, w⟩ setup.wordMemory constraints fetch
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.jumpBranchSlt = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left JumpBranchSlt.importedConstraints JumpBranchSlt.importedConstraintsTimestampLookups)
      have bounds := JumpBranchSlt.Proofs.rv_decoder_field_bounds fd
      exact jumpBranch_row_zero_preserving limbField ⟨.jumpBranchSlt, w⟩ core
        ⟨pc, bits, d⟩ fd query
        (JumpBranchSlt.Proofs.rv_decoder_selectors limbField core bounds.2.1 query)
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.mulDiv = kind at family
      subst kind
      exact mulDiv_row_zero_preserving limbField ⟨.mulDiv, w⟩ ⟨pc, bits, d⟩ fd query
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.shiftBinop = kind at family
      subst kind
      exact shiftBinop_row_zero_preserving limbField ⟨.shiftBinop, w⟩ ⟨pc, bits, d⟩ fd query
  · obtain ⟨d, fd, equal⟩ := h
    subst equal
    cases row with
    | mk kind w =>
      change PooledFamily.subwordMemory = kind at family
      subst kind
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (SubwordMemory.importedConstraints setup.subwordMemory)
          SubwordMemory.importedConstraintsTimestampLookups)
      exact subword_row_zero_preserving limbField ⟨.subwordMemory, w⟩ setup.subwordMemory core
        ⟨pc, bits, d⟩ fd query

/-- Every row of an accepted RV-decoded pooled trace preserves x0, from the public program image alone. -/
theorem rv_pooled_zero_preserving {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {addresses : List (BitVec 32)}
    {program : List RVPooledProgramEntry}
    (image : rvProgramImageWith rvPooledDecoderFields initial addresses = some program)
    (decoded : RVPooledDecoded trace program) : ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, present, family, query⟩ := rv_decoder_member (decoded row member)
  obtain ⟨_, _, _, _, fields⟩ := rvProgram_entry_fetch image entry present
  exact rv_pooled_row_zero_preserving hp trace.rom row (accepted.constraints row member) fields family query

end Airbender.Trace.RVZero
