import Airbender.Proofs.WordMemory

namespace Airbender.WordMemory
open Airbender.Arithmetic

-- Local claims only. Native Sail LW/SW and memory/ROM state binding are pending.
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

/-- SW's read port is rs2; LW's write port is rd. -/
theorem register_address {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p} (store : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (selected : w 10 = if store then 1 else 0) :
    (if store then w 19 else w 25) = (if store then w 6 else w 7) ∧
      (if store then w 20 else w 26) = 0 :=
  Proofs.register_address store h selected

/-- ROM means address < 4 MiB; satisfying rows exclude stores to that region. -/
theorem rom_selection {p : Nat} [Fact p.Prime] (hp : 131072 < p)
    {rom : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} (store : Bool) {address : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (selected : w 10 = if store then 1 else 0)
    (mapping : (if store then w 26 else w 20) = (address.hi : ZMod p))
    (addressBound : address.Bounded) :
    w 35 = (if address.hi < 64 then 1 else 0) ∧
      (store = true → 64 ≤ address.hi) :=
  Proofs.rom_selection hp store h selected mapping addressBound

/-- The single data query, after eliminating all compiler-created copies. -/
theorem data_lookup {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p} (store : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (selected : w 10 = if store then 1 else 0) :
    rom.Contains #[] #v[
      w 35 * ((if store then w 25 else w 19) + 65536 * (if store then w 26 else w 20)),
      w 31 - (1 - w 35) * w 23, w 32 - (1 - w 35) * w 24,
      0, 0, 0, 0, 0, w 4 * w 35 * 34] :=
  Proofs.data_lookup store h selected

/-- RAM loads/stores copy both data limbs. The external table must bind tag zero
    to zero outputs; this is a table-wide law, not an assumed circuit result. -/
theorem ram_data {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    (zeroRows : ∀ row, rom.Contains #[] row → row[8] = 0 → row[1] = 0 ∧ row[2] = 0)
    {w : Nat → ZMod p} (store : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (selected : w 10 = if store then 1 else 0) (ram : w 35 = 0) :
    w 31 = w 23 ∧ w 32 = w 24 :=
  Proofs.ram_data zeroRows store h selected ram

/-- Active ROM loads bind the written limbs to the program-table query. -/
theorem rom_data {p : Nat} [Fact p.Prime] {rom : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom))
    (selected : w 10 = 0) (active : w 4 = 1) (inROM : w 35 = 1) :
    rom.Contains #[] #v[w 19 + 65536 * w 20, w 31, w 32, 0, 0, 0, 0, 0, 34] :=
  Proofs.rom_data h selected active inROM

end Airbender.WordMemory
