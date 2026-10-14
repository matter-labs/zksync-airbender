import HumanSail.Machine

/-! The two hint encodings that overlap Airbender's base instructions (`add x0, x0, x2..x5`: Zihintntl;
`ori x0, rs1, imm`: Zicbop). Their decoder clauses only produce an instruction when the extension is on; these
lemmas say their field decoders are plain values whenever the field is valid, so the walker can step over them. -/

open Sail SailRV32 SailRV32.Functions

namespace Slop.Equiv

theorem ntl_pure (x : BitVec 5) (h : encdec_ntl_backwards_matches x = true) :
    ∃ a, encdec_ntl_backwards x = pure a := by
  unfold encdec_ntl_backwards_matches at h
  unfold encdec_ntl_backwards
  split
  all_goals first | exact ⟨_, rfl⟩ | (split at h <;> simp_all)

theorem cbop_pure (x : BitVec 5) (h : encdec_cbop_zicbop_backwards_matches x = true) :
    ∃ a, encdec_cbop_zicbop_backwards x = pure a := by
  unfold encdec_cbop_zicbop_backwards_matches at h
  unfold encdec_cbop_zicbop_backwards
  split
  all_goals first | exact ⟨_, rfl⟩ | (split at h <;> simp_all)

end Slop.Equiv
