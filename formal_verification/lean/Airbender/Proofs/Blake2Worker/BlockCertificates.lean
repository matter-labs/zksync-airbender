import Airbender.Proofs.Tables.ImportedBlocks
import Airbender.Proofs.Tables.LiteralSizes

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The same finite literal check, split into small16-element windows so a512
    element native block needs no larger recursion or proof/resource limit. -/
def checkBlockWindows (f : Nat → Nat) (start : Nat) (block : Block) : Bool :=
  (List.finRange ((block.length+15)/16)).all fun high =>
    (List.finRange 16).all fun low =>
      let n := high.val*16+low.val
      if n < block.length then block.get? n == some (f (start+n)) else true

def checkWindowBlocks (f : Nat → Nat) : Nat → List Block → Bool
  | _,[] => true
  | start,b::bs => checkBlockWindows f start b && checkWindowBlocks f (start+b.length) bs

theorem checkBlockWindows_sound (f : Nat → Nat) (start : Nat) (block : Block)
    (checked : checkBlockWindows f start block = true) (n : Nat) (bound : n < block.length) :
    block.get? n = some (f (start+n)) := by
  have highBound : n/16 < (block.length+15)/16 := by omega
  have lowBound : n%16 < 16 := Nat.mod_lt _ (by decide)
  have high := List.all_eq_true.mp checked ⟨n/16,highBound⟩ (by simp)
  have low := List.all_eq_true.mp high ⟨n%16,lowBound⟩ (by simp)
  have same : n/16*16+n%16 = n := by omega
  simpa only [same,if_pos bound,beq_iff_eq] using low

theorem checkWindowBlocks_sound (f : Nat → Nat) (start : Nat) (blocks : List Block)
    (checked : checkWindowBlocks f start blocks = true) : checkBlocks f start blocks = true := by
  induction blocks generalizing start with
  | nil => exact checkBlocks_nil f start
  | cons block rest ih =>
    rw [checkWindowBlocks,Bool.and_eq_true] at checked
    rw [checkBlocks_cons_iff]
    exact ⟨fun i => checkBlockWindows_sound f start block checked.1 i.val i.isLt,ih _ checked.2⟩

/-- Assemble singleton geometry without reducing a concrete stored block. -/
theorem singleton_length (block : Block) :
    ([block].map Block.length).sum = block.length := by simp

/-- A separately checked literal block can be assembled without evaluating its data again. -/
theorem check_singleton_of_size (f : Nat → Nat) (start : Nat) (block : Block) (size : Nat)
    (geometry : block.length = size)
    (reads : ∀ i : Fin size, block.get? i.val = some (f (start+i.val))) :
    checkBlocks f start [block] = true := by
  rw [checkBlocks_cons_iff]
  constructor
  · intro i
    exact reads ⟨i.val,by rw [← geometry]; exact i.isLt⟩
  · exact checkBlocks_nil _ _

end Airbender.Setup.Proofs
