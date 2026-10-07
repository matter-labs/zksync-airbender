import Airbender.Proofs.WordMemory

namespace Airbender.WordMemory
open Airbender.Arithmetic

-- Local claims only. Native Sail LW/SW and memory/ROM state binding are next.
-- Range queries supply final-PC bounds; memory-address/input bounds remain explicit.

theorem local_flags {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom)) :
    ∀ i : Fin 8, w (#v[4, 10, 35, 33, 34, 46, 47, 48][i]) = 0 ∨
      w (#v[4, 10, 35, 33, 34, 46, 47, 48][i]) = 1 :=
  Proofs.local_flags h

theorem local_ranges {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom)) :
    (w 36).val < limbBase ∧ (w 11).val < limbBase ∧ (w 12).val < limbBase :=
  Proofs.local_ranges h

theorem pc_successor {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {rom : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} {initial final : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (mapping : w 0 = (initial.lo : ZMod p) ∧ w 1 = (initial.hi : ZMod p) ∧
      final.lo = (w 11).val ∧ final.hi = (w 12).val)
    (initialBound : initial.Bounded) :
    final.value = initial.value + 4 ∧ initial.value + 4 < wordModulus ∧
      final.toBitVec = initial.toBitVec + 4 :=
  Proofs.pc_successor hp inverse h mapping initialBound

theorem effective_address {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {rom : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} (store : Bool)
    {source immediate address : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (selected : w 10 = if store then 1 else 0)
    (mapping : w 17 = (source.lo : ZMod p) ∧ w 18 = (source.hi : ZMod p) ∧
      w 8 = (immediate.lo : ZMod p) ∧ w 9 = (immediate.hi : ZMod p) ∧
      (if store then w 25 else w 19) = (address.lo : ZMod p) ∧
      (if store then w 26 else w 20) = (address.hi : ZMod p))
    (sourceBound : source.Bounded) (immediateBound : immediate.Bounded)
    (addressBound : address.Bounded) :
    address.toBitVec = source.toBitVec + immediate.toBitVec :=
  Proofs.effective_address hp inverse store h selected mapping sourceBound immediateBound addressBound

end Airbender.WordMemory
