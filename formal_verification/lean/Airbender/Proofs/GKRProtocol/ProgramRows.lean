import Airbender.Review.Helpers.Decoder.ProgramRows

namespace Airbender.Trace.NativeDecoder.ProgramRows.Proofs
open Airbender.Trace.NativeDecoder.ProgramRows

/-- A non-sentinel row of the program-derived decoder model has an actual
Sail-decoded public entry of the selected native family. This is a logical
fact about the Lean model; the Rust differential binding remains open. -/
theorem active_member {p : Nat} (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (family : PooledFamily) (query : Vector (ZMod p) 9)
    (member : query ∈ rows config initial text capacity family)
    (active : query ≠ sentinel) :
    ∃ entry ∈ programOf config initial text,
      entry.data.family = family ∧ query = entry.query := by
  rcases List.mem_append.mp member with source | padding
  · rcases List.mem_map.mp source with ⟨pair, inText, rowEq⟩
    rcases pair with ⟨bits, index⟩
    cases entryEq : wordEntry config initial bits index with
    | none =>
        have hs : query = sentinel := by simpa [familyRow, entryEq] using rowEq.symm
        exact (active hs).elim
    | some entry =>
        by_cases selected : entry.data.family = family
        · have inProgram : entry ∈ programOf config initial text := by
            exact List.mem_filterMap.mpr ⟨(bits, index), inText, entryEq⟩
          have hq : query = entry.query := by
            simpa [familyRow, entryEq, selected] using rowEq.symm
          exact ⟨entry, inProgram, selected, hq⟩
        · have hs : query = sentinel := by
            simpa [familyRow, entryEq, selected] using rowEq.symm
          exact (active hs).elim
  · have hs : query = sentinel := (List.mem_replicate.mp padding).2
    exact (active hs).elim

/-- The generic row lemma gives the existing logical decoder-table membership.
It does not claim that a Rust setup column equals this modeled row list. -/
theorem active_decoded {p : Nat} [Fact p.Prime] (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (family : PooledFamily) (query : Vector (ZMod p) 9)
    (member : query ∈ rows config initial text capacity family)
    (active : query ≠ sentinel) :
    (decoderTable (programOf config initial text) family).Contains #[] query := by
  obtain ⟨entry, inProgram, selected, hq⟩ :=
    active_member config initial text capacity family query member active
  apply (decoderTable (programOf config initial text) family).implied_by_completeness #[] query
  change ∃ entry ∈ programOf config initial text,
    entry.data.family = family ∧ query = entry.query
  exact ⟨entry, inProgram, selected, hq⟩

/-- The native 16-bit PC-limb range excludes the unsupported minus-one row
in the BabyBear field. -/
theorem bounded_pc_not_sentinel (query : Vector (ZMod babyBearModulus) 9)
    (bounded : query[0].val < 65536) : query ≠ sentinel := by
  intro equal
  have first := congrArg (fun row : Vector (ZMod babyBearModulus) 9 => row[0].val) equal
  have low : query[0].val = (-1 : ZMod babyBearModulus).val := by
    simpa [sentinel] using first
  have minusOne : (-1 : ZMod babyBearModulus).val = 2013265920 := by
    change (-1 : ZMod 2013265921).val = 2013265920
    exact ZMod.val_neg_one 2013265920
  have high : query[0].val = 2013265920 := by
    exact low.trans minusOne
  omega

/-- One program-independent membership result for every selected active
decoder row of the modeled full or reduced setup. -/
theorem bounded_pc_decoded [Fact babyBearModulus.Prime] (config : Config)
    (initial : Reference.RiscV.Sail.State) (text : List (BitVec 32))
    (capacity : Nat) (family : PooledFamily)
    (query : Vector (ZMod babyBearModulus) 9)
    (member : query ∈ rows config initial text capacity family)
    (bounded : query[0].val < 65536) :
    (decoderTable (programOf config initial text) family).Contains #[] query :=
  active_decoded config initial text capacity family query member
    (bounded_pc_not_sentinel query bounded)

end Airbender.Trace.NativeDecoder.ProgramRows.Proofs
