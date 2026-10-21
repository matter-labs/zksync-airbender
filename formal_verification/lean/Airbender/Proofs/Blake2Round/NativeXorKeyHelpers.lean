import Airbender.Review.Circuits.Blake2Round.Tables.XorData
import Airbender.Proofs.Tables.PeriodicColumns
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

def carryBase (kind : Fin 2) : Nat := #v[256, 128][kind]
def carryKind (kind : Fin 2) : Fin 6 := ⟨3 + kind.val, by omega⟩

namespace NativeXorKeyHelpers

theorem periodic_constant_get (b count n : Nat) (hb : 0 < b) (h : n < count * b) :
    Block.get? (.periodic count 1 (Array.replicate b 0)) n = some (n / b) := by
  have hm : n % b < b := Nat.mod_lt _ hb
  simp [Block.get?, Block.length, h, hm]
  simpa only [Int.natCast_ediv] using
    And.intro (Int.natCast_nonneg (n / b)) (Int.toNat_natCast (n / b))

theorem periodic_range_get (b count n : Nat) (hb : 0 < b) (h : n < count * b) :
    Block.get? (.periodic count 0 (Array.range b)) n = some (n % b) := by
  have hm : n % b < b := Nat.mod_lt _ hb
  simp [Block.get?, Block.length, h, hm]
  simpa only [Int.natCast_emod] using
    And.intro (Int.natCast_nonneg (n % b)) (Int.toNat_natCast (n % b))

theorem periodic_cyclic_get (b count first n : Nat) (hb : 0 < b) (h : n < count * b) :
    Block.get? (.periodic count 0 (Array.ofFn (fun i : Fin b => (first + i.val) % b))) n =
      some ((first + n % b) % b) := by
  have hm : n % b < b := Nat.mod_lt _ hb
  simp [Block.get?, Block.length, h, hm]
  simpa only [Int.natCast_emod, Int.natCast_add] using
    And.intro (Int.natCast_nonneg ((first + n) % b)) (Int.toNat_natCast ((first + n) % b))

theorem dense_range_get (length n : Nat) (hn : n < length) :
    Block.get? (.dense (Array.range length)) n = some n := by
  simp [Block.get?, Block.length, hn]

theorem dense_affine_get (length first n : Nat) (hn : n < length) :
    Block.get? (.dense (Array.ofFn (fun i : Fin length => first + i.val))) n =
      some (first + n) := by
  simp [Block.get?, Block.length, hn]

theorem affine_constant_get (length first n : Nat) (hn : n < length) :
    Block.get? (.affine length first 0) n = some first := by
  simp [Block.get?, Block.length, hn]

end NativeXorKeyHelpers

end Airbender.Blake2Round.Proofs
