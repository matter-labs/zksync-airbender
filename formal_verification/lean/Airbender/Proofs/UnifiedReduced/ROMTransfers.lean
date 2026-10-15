import Airbender.Proofs.UnifiedReduced.ROMRow
import Airbender.Proofs.UnifiedReduced.WordROM

namespace Airbender.UnifiedReduced.ROMView
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem row_transfers [Fact p.Prime] (hp : 131072 < p)
    (before : Reference.RiscV.Sail.State) (native : Trace.Row p UnifiedFamily)
    (setup : Table (ZMod p) (fields 10)) (active : native.assignment 4 = 1)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment native.assignment)
      (native.constraints setup)) :
    (row before native).reads = native.reads.map (Trace.ROMView.token before) ∧
      (row before native).writes = native.writes.map (Trace.ROMView.token before) := by
  obtain ⟨family, w⟩ := native
  cases family
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup) at holds
  have core := Verification.holds_of_sublist holds
    (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
  have one : (1 : ZMod p).val = 1 := by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have loadFlag : w 28 = 0 ∨ w 28 = 1 := Proofs.local_flags core 18
  have storeFlag : w 29 = 0 ∨ w 29 = 1 := Proofs.local_flags core 19
  rcases loadFlag with outside | load
  · rcases storeFlag with outsideStore | store
    · simp [row, outside, outsideStore, Row.reads, Row.writes, Row.ports, Row.columns,
        CircuitLayout.columns, CircuitLayout.ports, importedConstraintsMemoryPorts,
        importedConstraintsTraceColumns, readToken, writeToken, MemoryAddress.code,
        MemoryPort.readCode, MemoryPort.writeCode, pairCode, rawPair, Trace.ROMView.token,
        Trace.ROMView.shadow]
    · have high := (Proofs.word_rom_selection hp true core outside store).2 rfl
      have notROM : ¬(w 45).val < 64 := by omega
      simp [row, outside, store, Row.reads, Row.writes, Row.ports, Row.columns,
        CircuitLayout.columns, CircuitLayout.ports, importedConstraintsMemoryPorts,
        importedConstraintsTraceColumns, readToken, writeToken, MemoryAddress.code,
        MemoryPort.readCode, MemoryPort.writeCode, pairCode, rawPair, Trace.ROMView.token,
        Trace.ROMView.shadow, one, notROM]
  · have store : w 29 = 0 := Proofs.dispatch_exclusive (by omega) core active 16 load 17 (by decide)
    have classification := (Proofs.word_rom_selection hp false core load store).1
    change w 54 = (if (w 39).val < 64 then 1 else 0) at classification
    by_cases inside : (w 39).val < 64
    · have rom : w 54 = 1 := by simpa [inside] using classification
      have low := lt_trans (Trace.ROMView.public_word_bound before
        (Nat.pair 1 (Nat.pair (w 38).val (w 39).val))).1 (by change 65536 < p; omega)
      have high := lt_trans (Trace.ROMView.public_word_bound before
        (Nat.pair 1 (Nat.pair (w 38).val (w 39).val))).2 (by change 65536 < p; omega)
      simp [row, load, store, rom, Row.reads, Row.writes, Row.ports, Row.columns,
        CircuitLayout.columns, CircuitLayout.ports, importedConstraintsMemoryPorts,
        importedConstraintsTraceColumns, readToken, writeToken, MemoryAddress.code,
        MemoryPort.readCode, MemoryPort.writeCode, pairCode, rawPair, Trace.ROMView.token,
        Trace.ROMView.shadow, readData, one, inside, ZMod.val_natCast_of_lt low,
        ZMod.val_natCast_of_lt high]
    · have rom : w 54 = 0 := by simpa [inside] using classification
      simp [row, load, store, rom, Row.reads, Row.writes, Row.ports, Row.columns,
        CircuitLayout.columns, CircuitLayout.ports, importedConstraintsMemoryPorts,
        importedConstraintsTraceColumns, readToken, writeToken, MemoryAddress.code,
        MemoryPort.readCode, MemoryPort.writeCode, pairCode, rawPair, Trace.ROMView.token,
        Trace.ROMView.shadow, one, inside]

end Airbender.UnifiedReduced.ROMView
