import Airbender.Proofs.Trace.Families.WordMemory.ProjectedPorts
import Airbender.Proofs.Trace.Families.WordMemory.ProjectedInputs
import Airbender.Proofs.Trace.Platform
import Airbender.Proofs.Sail.VirtualMemory

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
open _root_.Sail.ArchSem

/-- Native bounded address limbs have exactly the public RV32 cell encoding. -/
theorem effective_cell_word {p : Nat} [Fact p.Prime] {rom : WordROM} {w : Nat → ZMod p}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    Word.ofBitVec (addressWord w).toBitVec = addressWord w := by
  have bounded : (addressWord w).Bounded := address_bounds native
  apply Word.eq_of_value (Word.ofBitVec_bound _) bounded
  rw [Word.ofBitVec_value, Word.toBitVec_toNat bounded]

/-- Native fixed queries give effective byte alignment, including RV32 rollover. -/
theorem effective_alignment {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {w : Nat → ZMod p}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    (addressWord w).toBitVec.toNat % 4 = 0 := by
  rw [Word.toBitVec_toNat (address_bounds native)]
  have low := (rom_values hp native).1
  change ((w 19).val + 65536 * (w 20).val) % 4 = 0
  omega

/-- The final store port targets the effective RAM cell. All address limbs and
    its space flag are derived from the imported native constraints. -/
theorem store_port_address {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {w : Nat → ZMod p}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (store : w 12 = 1) :
    importedConstraintsMemoryPorts[2].address.code w = (Cell.ram (addressWord w).toBitVec).addressCode := by
  have effects := transfers hp native
  have space : w 32 = 0 := by simpa only [store, sub_self] using effects.writeAddress.1
  have low : w 33 = w 19 := by simpa only [store, one_mul, sub_self, zero_mul, add_zero] using effects.writeAddress.2.1
  have high : w 34 = w 20 := by simpa only [store, one_mul] using effects.writeAddress.2.2
  have one : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (show 1 < p from by omega)
  simp only [Cell.addressCode]
  rw [effective_cell_word native]
  simp [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
    space, low, high, one, addressWord]

/-- A retained RAM-load port reads the effective address in the actual Sail
    instruction pre-state. No expected RAM value is supplied. -/
theorem projected_ram_read {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (load : w 12 = 0) (ram : 64 ≤ (w 20).val)
    {before after : State}
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) :
    (Cell.ram (addressWord w).toBitVec).read before =
      .ok (Word.mk (w 30).val (w 31).val).toBitVec before := by
  have effects := transfers hp native
  have low : w 28 = w 19 := by simpa only [load, sub_zero, one_mul, zero_mul, add_zero] using effects.readAddress.1
  have high : w 29 = w 20 := by simpa only [load, sub_zero, one_mul] using effects.readAddress.2
  have one : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (show 1 < p from by omega)
  have address : importedConstraintsMemoryPorts[1].address.code w =
      (Cell.ram (addressWord w).toBitVec).addressCode := by
    simp only [Cell.addressCode]
    rw [effective_cell_word native]
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
      load, low, high, one, addressWord]
  have kept : architecturalAddress (importedConstraintsMemoryPorts[1].address.code w) = true := by
    rw [address, architectural_ram, Word.toBitVec_toNat (address_bounds native)]
    simp only [Word.value, addressWord, limbBase]
    exact decide_eq_true (by omega)
  have read := projected_history_read hp epoch native history
    (port := importedConstraintsMemoryPorts[1])
    (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) kept address
  simpa [memoryWord, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate,
    importedConstraintsMemoryPorts, Nat.unpair_pair] using read

/-- Native stores copy rs2 into the final mixed-port write. Its actual Sail
    pre-state and result come from the projected history, not a write premise. -/
theorem projected_ram_write {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (store : w 12 = 1) {before after : State}
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) :
    run (writeMemory (size := 4) (addressWord w).toBitVec
      (Word.mk (w 30).val (w 31).val).toBitVec) before = .ok () after := by
  have written := projected_history_write hp epoch native history
    (port := importedConstraintsMemoryPorts[2]) rfl (store_port_address hp native store)
  have copied := (transfers hp native).store store
  simpa [Cell.write, memoryWord, MemoryPort.writeCode, WordColumns.code,
    WordColumns.evaluate, importedConstraintsMemoryPorts, Nat.unpair_pair, copied.2.1, copied.2.2] using written

/-- Actual native RAM loads traverse the original Sail translation, permission
    and platform path under public configuration and an ordinary address domain. -/
theorem projected_virtual_ram_read {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 4194304 < p) {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (load : w 12 = 0) (ram : 64 ≤ (w 20).val)
    (address : (addressWord w).toBitVec = (sourceWord w).toBitVec + (immediateWord w).toBitVec)
    {entry : ProgramEntry WordMemoryFamily}
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query)
    {before after : State} (configuration : FlatMemoryConfiguration before)
    (ordinary : OrdinaryWordAddress (addressWord w).toBitVec)
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) :
    run (SailRV32.Functions.vmem_read (.Regidx entry.data.rs1) (immediateWord w).toBitVec 4
      (.Load .Data) false false false) before =
      .ok (.Ok (Word.mk (w 30).val (w 31).val).toBitVec) before := by
  have read := projected_ram_read hp epoch native load ram history
  have aligned := effective_alignment hp native
  rw [address] at read aligned ordinary
  exact virtual_word_read configuration _ _ (projected_source_read hp epoch native history query)
    aligned ordinary read

/-- Actual native stores traverse the original Sail memory path and reach the
    same native-history state, with no expected write/state result premise. -/
theorem projected_virtual_ram_write {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 4194304 < p) {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (store : w 12 = 1)
    (address : (addressWord w).toBitVec = (sourceWord w).toBitVec + (immediateWord w).toBitVec)
    {entry : ProgramEntry WordMemoryFamily}
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query)
    {before after : State} (configuration : FlatMemoryConfiguration before)
    (ordinary : OrdinaryWordAddress (addressWord w).toBitVec)
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) :
    run (SailRV32.Functions.vmem_write (.Regidx entry.data.rs1) (immediateWord w).toBitVec 4
      (Word.mk (w 30).val (w 31).val).toBitVec (.Store .Data) false false false) before =
      .ok (.Ok true) after := by
  have written := projected_ram_write hp epoch native store history
  have aligned := effective_alignment hp native
  rw [address] at written aligned ordinary
  exact virtual_memory_write (Or.inr (Or.inr rfl)) configuration _ _
    (projected_source_read hp epoch native history query) aligned ordinary _ written

/-- Initialized native matching realizes a complete architectural history while
    retaining the actual public platform configuration at its final state. -/
theorem projected_platform_configuration {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {setup : DecoderSetup} {before : State}
    {cells : List Cell} {seeds : List ShadowSeed}
    (inputs : ShadowImageBoundary trace before cells seeds) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (configuration : FlatMemoryConfiguration before) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p WordMemoryFamily)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells
        ((rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) before after ∧
      SailStateMatches cells history after ∧ FlatMemoryConfiguration after := by
  obtain ⟨history, rows, after, complete, permutation, ordered, actual, matched⟩ :=
    projected_row_history hp inputs accepted decoded aligned
  exact ⟨history, rows, after, complete, permutation, ordered, actual, matched,
    Trace.Proofs.sail_history_configuration actual configuration⟩

end Airbender.WordMemory.Proofs
