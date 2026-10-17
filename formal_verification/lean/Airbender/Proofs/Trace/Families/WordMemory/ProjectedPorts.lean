import Airbender.Proofs.Trace.PortProjection
import Airbender.Proofs.Trace.Families.WordMemory.ShadowImage

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification

/-- Native loads write GPRs; stores target RAM outside the ROM prefix. Thus the
    actual final port is always architectural, independently of shadow values. -/
theorem native_destination_kept {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {w : Nat → ZMod p}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    architecturalAddress (importedConstraintsMemoryPorts[2].address.code w) = true := by
  have effects := transfers hp native
  rcases effects.storeBit with load | store
  · change w 12 = 0 at load
    have space : w 32 = 1 := by simpa only [load, sub_zero] using effects.writeAddress.1
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, architecturalAddress,
      shadow, Nat.unpair_pair, space]
  · change w 12 = 1 at store
    have space : w 32 = 0 := by simpa only [store, sub_self] using effects.writeAddress.1
    have high : w 34 = w 20 := by simpa only [store, one_mul] using effects.writeAddress.2.2
    have outside := (effects.store store).1
    have oneNat : ((1 : Nat) : ZMod p).val = 1 :=
      ZMod.val_natCast_of_lt (show 1 < p from by omega)
    have one : (1 : ZMod p).val = 1 := by simpa only [Nat.cast_one] using oneNat
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, architecturalAddress,
      shadow, Nat.unpair_pair, space, high, one, Nat.not_lt.mpr outside]

/-- Retained native ports read one actual instruction pre-state. Erased ROM
    shadows require no Sail read; all native matching still includes them. -/
theorem projected_history_read {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {cells : List Cell} {row : Row p WordMemoryFamily} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (row.constraints rom))
    {before after : State}
    (history : SailHistory cells ((rowEvents epoch row).reverse.filter
      fun event => architecturalAddress event.2.1) before after)
    {port : MemoryPort} (present : port ∈ row.ports)
    (kept : architecturalAddress (port.address.code row.assignment) = true)
    {cell : Cell} (address : port.address.code row.assignment = cell.addressCode) :
    cell.read before = .ok (memoryWord (port.readCode row.assignment)) before := by
  cases row with
  | mk family w =>
    cases family
    exact Trace.Proofs.projected_native_read epoch architecturalAddress rfl rfl rfl
      (native_destination_kept hp native) history present kept address

/-- The final native mixed-port write survives projection and updates the actual
    Sail pre-state, including hardwired x0 masking. -/
theorem projected_history_write {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {cells : List Cell} {row : Row p WordMemoryFamily} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (row.constraints rom))
    {before after : State}
    (history : SailHistory cells ((rowEvents epoch row).reverse.filter
      fun event => architecturalAddress event.2.1) before after)
    {port : MemoryPort} (last : row.ports.toList.getLast? = some port)
    {cell : Cell} (address : port.address.code row.assignment = cell.addressCode) :
    run (cell.write (memoryWord (port.writeCode row.assignment))) before = .ok () after := by
  cases row with
  | mk family w =>
    cases family
    have finalPort : port = importedConstraintsMemoryPorts[2] := by
      change some importedConstraintsMemoryPorts[2] = some port at last
      exact (Option.some.inj last).symm
    subst port
    exact Trace.Proofs.projected_native_write epoch architecturalAddress rfl rfl rfl
      (native_destination_kept hp native) history address

/-- Original public decoder indices identify the retained source GPR and its
    actual Sail read even when the native shadow port is erased. -/
theorem projected_source_read {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    {before after : State}
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after)
    {entry : ProgramEntry WordMemoryFamily}
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok (sourceWord w).toBitVec before := by
  have source := (Trace.Proofs.native_query_indices (by dsimp [limbBase]; omega) query).1
  change (w 5).val = entry.data.rs1.toNat at source
  have read := projected_history_read hp epoch native history
    (port := importedConstraintsMemoryPorts[0])
    (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    (by simp [importedConstraintsMemoryPorts, MemoryAddress.code,
      architecturalAddress, shadow, Nat.unpair_pair])
    (cell := Cell.register entry.data.rs1)
    (by change Nat.pair 0 (Nat.pair (w 5).val 0) = Nat.pair 0 (Nat.pair entry.data.rs1.toNat 0)
        rw [source])
  simpa [Cell.read, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate,
    importedConstraintsMemoryPorts, memoryWord, Nat.unpair_pair, sourceWord] using read

end Airbender.WordMemory.Proofs
