module
public import Slop.WordMemory
public import Slop.Trace.Addresses
public import Human.Helpers.Memory.Native
public import Slop.Trace.Family.History

@[expose] public section

namespace Airbender.Trace.ROMView
open Arithmetic

def readData (w : Nat → ZMod p) (lo hi : ZMod p) : Nat → ZMod p :=
  fun i => if i = WordMemory.Variables.readDataLo then lo
    else if i = WordMemory.Variables.readDataHi then hi else w i

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
/-- ROM loads do not use the native read-value columns in any retained
    equation, lookup or clock constraint. Replacing them preserves exactly
    the same imported Clean relation; no compiler correspondence is involved. -/
theorem read_data_unused {p : Nat} [Fact p.Prime]
    {rom : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (load : w WordMemory.Variables.storeSelector = 0)
    (inROM : w WordMemory.Variables.romSelector = 1) (lo hi : ZMod p) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (readData w lo hi))
      (WordMemory.clockConstraints rom) ↔
    FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.clockConstraints rom) := by
  simp [WordMemory.clockConstraints, WordMemory.importedConstraints,
    WordMemory.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, readData, Lookup.Contains,
    Verification.range16, timestampLookup, Table.toRaw, load, inROM]

theorem native_clocks {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] (hp : 4 < p)
    {trace : Data p Kind} {cells : List Cell}
    (seed : trace.initialMemory = nativeBootImage cells)
    (initial : trace.initial = PCState.boundary 0 (4, 0)) : ClockBoundary trace := by
  constructor
  · rw [initial]
    change (4 : ZMod p).val < timestampBase ∧ (0 : ZMod p).val < timestampBase
    rw [ZMod.val_ofNat_of_lt hp]
    norm_num [timestampBase]
  · rw [initial]
    change ((4 : ZMod p).val + timestampBase * (0 : ZMod p).val) % 4 = 0
    rw [ZMod.val_ofNat_of_lt hp]
    norm_num
  · intro native member
    rw [seed] at member
    obtain ⟨cell, _, rfl⟩ := List.mem_map.mp member
    simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]

theorem native_addresses {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    [Proofs.ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (clocks : ClockBoundary trace) {cells : List Cell}
    (seed : trace.initialMemory = nativeBootImage cells) :
    ∀ native ∈ trace.rows, ∀ port ∈ native.ports,
      (port.address.word native.assignment).Bounded := by
  intro native member port present
  have initialized := Proofs.initialized_addresses hp inverse accepted clocks native member port present
  rw [seed] at initialized
  have addresses : (nativeBootImage (p := p) cells).map MemoryToken.address =
      cells.map Cell.addressCode := by
    simp [nativeBootImage, List.map_map, Cell.initialToken]
  rw [addresses] at initialized
  obtain ⟨cell, _, equal⟩ := List.mem_map.mp initialized
  rw [Proofs.address_word equal.symm]
  exact Proofs.cell_address_bound cell

theorem shadow_ram (address : BitVec 32) :
    shadow (Cell.ram address).addressCode ↔ address.toNat < ROM.limit := by
  simp only [shadow, Cell.addressCode, Nat.unpair_pair, true_and, Word.ofBitVec]
  change address.toNat / 65536 < 64 ↔ address.toNat < 4194304
  omega

end Airbender.Trace.ROMView
