import Airbender.Proofs.Trace.PortProjection
import Airbender.Proofs.ReducedMachine.NativeWordMemoryDomains
import Airbender.Review.Circuits.ReducedMachine.WordMemoryResult

namespace Airbender.ReducedMachine.NativeWordMemoryProjectedPortProofs
open Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

abbrev events (epoch : Nat) (w : Nat → ZMod mersenne31Modulus) :=
  Trace.nativeRowEvents epoch importedConstraintsTraceColumns importedConstraintsMemoryPorts w

/-- Every retained actual port reads ONE original pre-state. Native readonly
    refreshes stutter even for RAM and aliases; ignored ROM shadows stay native. -/
theorem retained_reads {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {cells : List Cell} (epoch : Nat) {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells ((events epoch w).reverse.filter
      fun event => architecturalAddress event.2.1) before after) :
    ∀ i : Fin 3, (wordMemoryPortDomains w entry)[i] = true →
      (wordMemoryPortCells w entry)[i].read before =
        .ok (memoryWord (importedConstraintsMemoryPorts[i].readCode w)) before := by
  have domains := NativeWordMemoryDomainProofs.port_domains holds fields query
  have destination : architecturalAddress (importedConstraintsMemoryPorts[2].address.code w) = true := by
    simpa [wordMemoryPortDomains] using domains 2
  intro i kept
  have present : importedConstraintsMemoryPorts[i] ∈ importedConstraintsMemoryPorts := by
    fin_cases i <;> simp [importedConstraintsMemoryPorts]
  exact Trace.Proofs.projected_native_read epoch architecturalAddress rfl
    NativeWordMemoryPortProofs.readonly_sources.1 NativeWordMemoryPortProofs.readonly_sources.2
    destination history present ((domains i).trans kept) (NativeWordMemoryPortProofs.addresses holds fields query i)

/-- The retained final GPR/RAM port writes that same pre-state. All earlier
    readonly transfers, including a RAM refresh, are proved data stutters. -/
theorem destination_write {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {cells : List Cell} (epoch : Nat) {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells ((events epoch w).reverse.filter
      fun event => architecturalAddress event.2.1) before after) :
    run ((wordMemoryPortCells w entry)[2].write (wordMemoryWrittenWord w).toBitVec) before = .ok () after := by
  have domains := NativeWordMemoryDomainProofs.port_domains holds fields query
  have destination : architecturalAddress (importedConstraintsMemoryPorts[2].address.code w) = true := by
    simpa [wordMemoryPortDomains] using domains 2
  have written := Trace.Proofs.projected_native_write epoch architecturalAddress rfl
    NativeWordMemoryPortProofs.readonly_sources.1 NativeWordMemoryPortProofs.readonly_sources.2
    destination history (NativeWordMemoryPortProofs.addresses holds fields query 2)
  simpa [memoryWord,MemoryPort.writeCode,WordColumns.code,WordColumns.evaluate,
    importedConstraintsMemoryPorts,Nat.unpair_pair,wordMemoryWrittenWord] using written

theorem source_read {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {cells : List Cell} (epoch : Nat) {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells ((events epoch w).reverse.filter
      fun event => architecturalAddress event.2.1) before after) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before = .ok (sourceWord w).toBitVec before := by
  have read := retained_reads epoch holds fields query history 0 (by simp [wordMemoryPortDomains])
  simpa [wordMemoryPortCells,Cell.read,memoryWord,MemoryPort.readCode,WordColumns.code,
    WordColumns.evaluate,importedConstraintsMemoryPorts,Nat.unpair_pair,sourceWord,source1,
    NativePortProofs.source_columns] using read

theorem store_second_read {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {cells : List Cell} (epoch : Nat) {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (store : entry.data.family = true)
    (history : SailHistory cells ((events epoch w).reverse.filter
      fun event => architecturalAddress event.2.1) before after) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before = .ok (wordMemorySecondWord w).toBitVec before := by
  have read := retained_reads epoch holds fields query history 1 (by simp [wordMemoryPortDomains,store])
  simpa [wordMemoryPortCells,store,Cell.read,memoryWord,MemoryPort.readCode,WordColumns.code,
    WordColumns.evaluate,importedConstraintsMemoryPorts,Nat.unpair_pair,wordMemorySecondWord] using read

theorem ram_load_read {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {cells : List Cell} (epoch : Nat) {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (load : entry.data.family = false)
    (ram : 64 ≤ (wordMemoryAddressWord w).hi)
    (history : SailHistory cells ((events epoch w).reverse.filter
      fun event => architecturalAddress event.2.1) before after) :
    (Cell.ram (wordMemoryAddressWord w).toBitVec).read before = .ok (wordMemorySecondWord w).toBitVec before := by
  have read := retained_reads epoch holds fields query history 1 (by simp [wordMemoryPortDomains,load,ram])
  simpa [wordMemoryPortCells,load,memoryWord,MemoryPort.readCode,WordColumns.code,
    WordColumns.evaluate,importedConstraintsMemoryPorts,Nat.unpair_pair,wordMemorySecondWord] using read

end Airbender.ReducedMachine.NativeWordMemoryProjectedPortProofs
