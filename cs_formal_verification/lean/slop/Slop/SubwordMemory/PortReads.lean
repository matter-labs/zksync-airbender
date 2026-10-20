import Slop.SubwordMemory.Values
import Slop.Trace.PortReads

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

abbrev nativeEvents (epoch : Nat) (w : Nat → ZMod p) :=
  Trace.nativeRowEvents epoch importedConstraintsTraceColumns importedConstraintsMemoryPorts w

/-- Query membership identifies rs1; native equations identify the opposite
    register port (rs2 for stores, rd for loads). -/
theorem source_address {p : Nat} (hp : limbBase < p) {w : Nat → ZMod p} {entry : ProgramEntry}
    (query : decoderQuery w = entry.query) :
    importedConstraintsMemoryPorts[0].address.code w = (Cell.register entry.data.rs1).addressCode := by
  have index := (Trace.Proofs.native_query_indices hp query).1
  change (w 5).val = entry.data.rs1.toNat at index
  simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, index]

theorem opposite_register_address {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} {entry : ProgramEntry} (store : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 10 = if store then 1 else 0) (query : decoderQuery w = entry.query) :
    (if store then importedConstraintsMemoryPorts[1] else importedConstraintsMemoryPorts[2]).address.code w =
      (Cell.register (if store then entry.data.rs2 else entry.data.rd)).addressCode := by
  have indices := Trace.Proofs.native_query_indices hp query
  change (w 5).val = entry.data.rs1.toNat ∧ (w 6).val = entry.data.rs2.toNat ∧
    (w 7).val = entry.data.rd.toNat at indices
  have wiring := register_address store h selected
  cases store <;> simp only [Bool.false_eq_true, if_false, if_true] at selected wiring ⊢
  all_goals simp [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, Cell.addressCode,
    selected, wiring.1, wiring.2, indices.2.1, indices.2.2]

theorem source_read {p : Nat} (hp : limbBase < p) {w : Nat → ZMod p} {entry : ProgramEntry}
    {cells : List Cell} (epoch : Nat) {before after : State}
    (query : decoderQuery w = entry.query)
    (history : Trace.SailHistory cells (nativeEvents epoch w).reverse before after) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok (Trace.memoryWord (importedConstraintsMemoryPorts[0].readCode w)) before :=
  Trace.Proofs.native_history_read epoch rfl rfl rfl history
    (by simp [importedConstraintsMemoryPorts]) (source_address hp query)

theorem register_read {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} {entry : ProgramEntry} (store : Bool)
    {cells : List Cell} (epoch : Nat) {before after : State}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 10 = if store then 1 else 0) (query : decoderQuery w = entry.query)
    (history : Trace.SailHistory cells (nativeEvents epoch w).reverse before after) :
    run (SailRV32.Functions.rX_bits (.Regidx (if store then entry.data.rs2 else entry.data.rd))) before =
      .ok (Trace.memoryWord ((if store then importedConstraintsMemoryPorts[1] else importedConstraintsMemoryPorts[2]).readCode w)) before := by
  apply Trace.Proofs.native_history_read epoch rfl rfl rfl history
    (by cases store <;> simp [importedConstraintsMemoryPorts])
    (opposite_register_address hp store h selected query)

theorem destination_write {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} {entry : ProgramEntry}
    {cells : List Cell} (epoch : Nat) {before after : State}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (load : w 10 = 0) (query : decoderQuery w = entry.query)
    (history : Trace.SailHistory cells (nativeEvents epoch w).reverse before after) :
    run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (Trace.memoryWord (importedConstraintsMemoryPorts[2].writeCode w))) before = .ok () after :=
  Trace.Proofs.native_history_write epoch rfl rfl rfl history rfl
    (opposite_register_address hp false h load query)

/-- Matching roots the RAM port at a public aligned cell, deriving the actual
    canonical byte address. No address-limb bound is supplied as a premise. -/
theorem ram_cell {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : NativeTrace p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell} (image : initialImage initial cells = some trace.initialMemory)
    {w : Nat → ZMod p} (member : (⟨.subwordMemory, w⟩ : Row p TraceKind) ∈ trace.rows)
    (store : Bool) (selected : w 10 = if store then 1 else 0) :
    let port := (if store then importedConstraintsMemoryPorts[2] else importedConstraintsMemoryPorts[1])
    Cell.ram (port.address.word w).toBitVec ∈ cells ∧
      port.address.code w = (Cell.ram (port.address.word w).toBitVec).addressCode := by
  apply Trace.Proofs.row_ram_cell hp inverse accepted boundary image member
    (by cases store <;> simp [Row.ports, importedConstraintsMemoryPorts])
  cases store with
  | false =>
    refine ⟨Nat.pair (w 21).val (w 22).val, ?_⟩
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, selected, ZMod.val_one]
  | true =>
    refine ⟨Nat.pair (w 27).val (w 28).val, ?_⟩
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, selected, ZMod.val_one]

theorem ram_read {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : NativeTrace p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell} (image : initialImage initial cells = some trace.initialMemory)
    {w : Nat → ZMod p} (member : (⟨.subwordMemory, w⟩ : Row p TraceKind) ∈ trace.rows)
    (store : Bool) (selected : w 10 = if store then 1 else 0)
    {before after : State}
    (history : Trace.SailHistory cells (nativeEvents trace.memoryEpoch w).reverse before after) :
    let port := (if store then importedConstraintsMemoryPorts[2] else importedConstraintsMemoryPorts[1])
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 (port.address.word w).toBitVec.toNat).run before =
      .ok (Trace.memoryWord (port.readCode w)) before := by
  exact Trace.Proofs.native_history_read trace.memoryEpoch rfl rfl rfl history
    (by cases store <;> simp [importedConstraintsMemoryPorts])
    (ram_cell hp inverse accepted boundary image member store selected).2

theorem ram_write {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : NativeTrace p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell} (image : initialImage initial cells = some trace.initialMemory)
    {w : Nat → ZMod p} (member : (⟨.subwordMemory, w⟩ : Row p TraceKind) ∈ trace.rows)
    (store : w 10 = 1) {before after : State}
    (history : Trace.SailHistory cells (nativeEvents trace.memoryEpoch w).reverse before after) :
    run (writeMemory (size := 4) (importedConstraintsMemoryPorts[2].address.word w).toBitVec
      (Trace.memoryWord (importedConstraintsMemoryPorts[2].writeCode w))) before = .ok () after :=
  Trace.Proofs.native_history_write trace.memoryEpoch rfl rfl rfl history rfl
    (ram_cell hp inverse accepted boundary image member true store).2

end Airbender.SubwordMemory.Proofs
