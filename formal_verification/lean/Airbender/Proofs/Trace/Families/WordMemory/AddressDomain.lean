import Airbender.Proofs.Trace.Families.WordMemory.MemoryTransport
import Airbender.Proofs.Trace.Families.WordMemory.CodeHistory

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Verification

/-- Native matching roots the effective RAM address in the public architectural
    cells or the independent shadow seeds. No per-row address domain is assumed. -/
theorem effective_public_cell {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    (inputs : ShadowImageBoundary trace initial cells seeds) (accepted : Accepted trace)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily) ∈ trace.rows) :
    Cell.ram (addressWord w).toBitVec ∈ cells ∨
      ∃ seed ∈ seeds, seed.1 = (addressWord w).toBitVec := by
  have native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints trace.rom) :=
    accepted.constraints _ member
  have effects := transfers hp native
  have one : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (show 1 < p from by omega)
  have port : ∃ port ∈ (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).ports,
      port.address.code w = (Cell.ram (addressWord w).toBitVec).addressCode := by
    rcases effects.storeBit with load | store
    · have low : w 28 = w 19 := by
        simpa only [load, sub_zero, one_mul, zero_mul, add_zero] using effects.readAddress.1
      have high : w 29 = w 20 := by
        simpa only [load, sub_zero, one_mul] using effects.readAddress.2
      refine ⟨importedConstraintsMemoryPorts[1], by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts], ?_⟩
      simp only [Cell.addressCode]
      rw [effective_cell_word native]
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, load, low, high, one, addressWord]
    · exact ⟨importedConstraintsMemoryPorts[2], by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts],
        store_port_address hp native store⟩
  obtain ⟨port, present, target⟩ := port
  have origin := Trace.Proofs.initialized_addresses (by dsimp [timestampBase]; omega)
    accepted (shadow_clock_boundary (by omega) inputs) _ member port present
  obtain ⟨token, tokenMember, address⟩ := List.mem_map.mp origin
  obtain ⟨tokens, image, combined⟩ := shadow_image_parts inputs
  rw [combined] at tokenMember
  rcases List.mem_append.mp tokenMember with real | ghost
  · obtain ⟨cell, cellMember, _, _, same⟩ := Trace.Proofs.image_sources image token real
    rw [same] at address
    have equal := Trace.Proofs.cell_address_injective (address.trans target)
    exact Or.inl (equal ▸ cellMember)
  · obtain ⟨seed, seedMember, rfl⟩ := List.mem_map.mp ghost
    change (Cell.ram seed.1).addressCode = port.address.code w at address
    have equal := Trace.Proofs.cell_address_injective (address.trans target)
    have same : seed.1 = (addressWord w).toBitVec := by simpa only [Cell.ram.injEq] using equal
    exact Or.inr ⟨seed, seedMember, same⟩

/-- A public ordinary-RAM domain and actual ROM-prefix coverage of public shadow
    seeds discharge every local address condition through accepted matching. -/
theorem initialized_address_domains {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {romCount : Nat} (inputs : ShadowImageBoundary trace initial cells seeds)
    (accepted : Accepted trace)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (covered : ∀ seed ∈ seeds, seed.1.toNat < 4 * romCount)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily) ∈ trace.rows) :
    (64 ≤ (w 20).val → OrdinaryWordAddress (addressWord w).toBitVec) ∧
    ((addressWord w).hi < 64 → (addressWord w).value < 4 * romCount) := by
  have native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints trace.rom) :=
    accepted.constraints _ member
  have canonical := Word.toBitVec_toNat (show (addressWord w).Bounded from address_bounds native)
  have low := (address_bounds native).1
  rcases effective_public_cell hp inputs accepted member with real | ⟨seed, present, same⟩
  · have outside := architectural_ram_domain inputs.architectural _ real
    refine ⟨fun _ => ordinary _ real, ?_⟩
    intro region
    rw [canonical] at outside
    dsimp [addressWord, Word.value, limbBase] at outside low region
    omega
  · have inside := inputs.shadows seed present
    rw [same, canonical] at inside
    refine ⟨?_, ?_⟩
    · intro ram
      dsimp [addressWord, Word.value, limbBase] at inside
      omega
    · intro _
      have bound := covered seed present
      rwa [same, canonical] at bound

end Airbender.WordMemory.Proofs
