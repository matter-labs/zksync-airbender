import Airbender.Proofs.Blake2Worker.NativeFixedResults

namespace Airbender.Blake2Worker.Fixed
open Verification

/-- The actual complete worker pool derives its tag and both operand domains.
    Worker query projection and execution remain separate. -/
theorem input_properties (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query) :
    ∃ kind : Kind, query[3].val = kind.tag ∧ query[0].val < kind.bound ∧ query[1].val < kind.bound := by
  exact FixedProofs.inputs query member

/-- Reuse byte semantics only after exact newly exported literal column binding. -/
theorem byte_xor (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (4 : ZMod mersenne31Modulus)) :
    query[0].val < 256 ∧ query[1].val < 256 ∧ query[2].val < 256 ∧
      BitVec.ofNat 8 query[2].val = byteOperation 4 (BitVec.ofNat 8 query[0].val) (BitVec.ofNat 8 query[1].val) := by
  exact FixedProofs.byte_result query member selected

theorem three_xor (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (26 : ZMod mersenne31Modulus)) :
    query[2].val = query[0].val ^^^ query[1].val := by
  exact FixedProofs.three_result query member selected

theorem four_xor (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (27 : ZMod mersenne31Modulus)) :
    query[2].val = query[0].val ^^^ query[1].val := by
  exact FixedProofs.four_result query member selected

/-- Exact output semantics of the newly exported native literal region. -/
theorem seven_xor (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (28 : ZMod mersenne31Modulus)) :
    query[2].val = query[0].val ^^^ query[1].val := by
  exact FixedProofs.seven_result query member selected

/-- Exact output semantics of the newly exported native literal region. -/
theorem nine_xor (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (29 : ZMod mersenne31Modulus)) :
    query[2].val = query[0].val ^^^ query[1].val := by
  exact FixedProofs.nine_result query member selected

end Airbender.Blake2Worker.Fixed
