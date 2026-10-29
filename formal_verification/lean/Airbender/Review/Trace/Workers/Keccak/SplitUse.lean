import Airbender.Review.Helpers.Delegation.SplitCaller
import Airbender.Review.Helpers.Memory.ROM

namespace Airbender.Keccak.Split
open Airbender.Trace Reference.RiscV.Sail Reference.Sail

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

def AtPC (state : State) (pc : BitVec 32) : Prop :=
  run (SailRV32.Functions.get_arch_pc ()) state = .ok pc state

/-- The first native call may only be reached from the wrapper entry. This is
one public initial-state condition, independent of any native witness. -/
def SafeInitialEntry (bundles : List Bundle) (initial : State) : Prop :=
  ∀ bundle ∈ bundles, ∀ index : Fin 361,
    0 < index.val → ¬ AtPC initial (bundle.callPC index.val)

/-- The blessed ABI carries the progressing control in x10 and a 256-byte
aligned state pointer in x11. These are assertions about successful reference
reads at an actual call, not supplied native controller or memory columns. -/
def ArgumentsAt (index : Nat) (state : State) : Prop :=
  ∃ control pointer : BitVec 32,
    (Cell.register 10).read state = .ok control state ∧
    (Cell.register 11).read state = .ok pointer state ∧
    control = BitVec.ofNat 32 (controlAt index) ∧
    ROM.limit ≤ pointer.toNat ∧ pointer.toNat % 256 = 0

end Airbender.Keccak.Split
