import Airbender.Review.Helpers.Delegation.SplitCaller
import Airbender.Review.Helpers.Memory.ROM

namespace Airbender.Keccak.Split
open Airbender.Trace

/-- One public 361-call wrapper interval. Worker state and output are not
encoded in the descriptor. -/
structure Bundle where
  start : BitVec 32

def Bundle.callPC (bundle : Bundle) (index : Nat) : BitVec 32 :=
  bundle.start + BitVec.ofNat 32 (4 * index)

/-- Code shape and complete caller coverage for blessed split permutations.
The separate supported-use condition must additionally establish legal entry,
256-byte state-pointer alignment and controller values along all public
reference prefixes. Those are not consequences of this syntax alone. -/
structure Shapes (callers : List Caller.ProgramEntry) (bundles : List Bundle) : Prop where
  bounds : ∀ bundle ∈ bundles,
    bundle.start.toNat % 4 = 0 ∧ bundle.start.toNat + 4 * 361 ≤ ROM.limit
  calls : ∀ bundle ∈ bundles, ∀ index : Fin 361,
    ∃ entry ∈ callers, entry.pc = bundle.callPC index.val ∧
      entry.data.family = kindAt index.val ∧
      entry.instruction = Caller.instruction (kindAt index.val)
  coverage : ∀ entry ∈ callers, ∃ bundle ∈ bundles,
    ∃ index : Fin 361,
      entry.pc = bundle.callPC index.val ∧ entry.data.family = kindAt index.val
  disjoint : ∀ one ∈ bundles, ∀ two ∈ bundles,
    ∀ i j : Fin 361,
      one.callPC i.val = two.callPC j.val → one = two ∧ i.val = j.val

end Airbender.Keccak.Split
