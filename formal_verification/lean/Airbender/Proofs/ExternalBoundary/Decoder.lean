import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Context.ExternalBoundary.Decoder

namespace Airbender.ExternalBoundary.Decoder.Proofs
open Trace
set_option warningAsError true

theorem typed_limb_ne_filler [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536) (limb : Fin 65536) :
    (limb.val : ZMod p) ≠ -1 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  intro equal
  have values := congrArg ZMod.val equal
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_neg_one n] at values
  omega

theorem decoded {Kind : Type} [DecidableEq Kind] [CircuitLayout Kind] [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 65536) {trace : Data p Kind} {program : List (ProgramEntry Kind)}
    {rows : Rows p Kind} {column : Fin 9} (binding : Binding trace program rows column) :
    ∀ row ∈ trace.rows, (decoderTable program row.family).Contains #[] row.decoderQuery := by
  intro row member
  rcases binding.contents row.family row.decoderQuery (binding.lookups row member) with real | filler
  · obtain ⟨entry, present, family, value⟩ := real
    have filtered : entry ∈ program.filter (fun e => e.data.family == row.family) := by
      simp [present, family]
    obtain ⟨index, equal⟩ := List.mem_iff_get.mp filtered
    change ∃ i : Fin (program.filter fun e => e.data.family == row.family).length, _
    exact ⟨index, value.trans (congrArg ProgramEntry.query equal).symm⟩
  · obtain ⟨limb, equal⟩ := binding.typed row member
    exact False.elim (typed_limb_ne_filler hp limb (equal.symm.trans filler))

end Airbender.ExternalBoundary.Decoder.Proofs
