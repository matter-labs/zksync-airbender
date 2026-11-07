import Airbender.Proofs.ReducedMachine.NativeWordMemoryProjectedPorts
import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryCodeHistory
import Airbender.Proofs.ReducedMachine.NativeWordMemoryDecodedResult
import Airbender.Review.Helpers.Memory.ReducedMachineWordMemoryTransfers

namespace Airbender.ReducedMachine.NativeWordMemoryTransferProofs
open Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The original x0 write accessor discards any value, not just native zero. -/
theorem zero_register_write (before : State) (value : BitVec 32) :
    run (SailRV32.Functions.wX_bits (.Regidx 0) value) before = .ok () before := by
  rw [write_zero]
  rfl

/-- The actual masked native write gives the ORIGINAL unmasked Sail load write.
    For rd=x0 the retained accessor discards the loaded value after its read. -/
theorem load_register_write {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {cells : List Cell} (epoch : Nat) {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (load : entry.data.family = false)
    (history : SailHistory cells ((NativeWordMemoryProjectedPortProofs.events epoch w).reverse.filter
      fun event => architecturalAddress event.2.1) before after) :
    run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd) (wordMemoryLoadWord w).toBitVec) before = .ok () after := by
  have written := NativeWordMemoryProjectedPortProofs.destination_write epoch holds fields query history
  have actual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd) (wordMemoryWrittenWord w).toBitVec)
      before = .ok () after := by simpa [wordMemoryPortCells,load,Cell.write] using written
  by_cases zero : entry.data.rd = 0
  · rw [zero] at actual
    have unchanged := zero_register_write before (wordMemoryWrittenWord w).toBitVec
    have same := (EStateM.Result.ok.inj (unchanged.symm.trans actual)).2
    subst after
    rw [zero]
    exact zero_register_write before _
  · have result := NativeWordMemoryResultProofs.written_result holds fields query
    simpa only [wordMemoryResult,load,Bool.false_eq_true,if_false,if_neg zero,result] using actual

/-- SW's actual memory write copies original rs2, never a dummy rd/x0 value. -/
theorem store_memory_write {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {cells : List Cell} (epoch : Nat) {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (store : entry.data.family = true)
    (history : SailHistory cells ((NativeWordMemoryProjectedPortProofs.events epoch w).reverse.filter
      fun event => architecturalAddress event.2.1) before after) :
    run (writeMemory (size := 4) (wordMemoryAddressWord w).toBitVec (wordMemorySecondWord w).toBitVec)
      before = .ok () after := by
  have written := NativeWordMemoryProjectedPortProofs.destination_write epoch holds fields query history
  have result : wordMemoryWrittenWord w = wordMemorySecondWord w := by
    simpa [wordMemoryResult,store] using NativeWordMemoryResultProofs.written_result holds fields query
  simpa [wordMemoryPortCells,store,Cell.write,result] using written

/-- Fresh native alignment/bounds and constructed ROM bytes transported through
    actual past history derive the architectural ROM load; no shadow equality. -/
theorem rom_load_read {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {cells : List Cell} {initial before : State} {pastEvents : List MemoryAccess}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (load : entry.data.family = false)
    (inside : (wordMemoryAddressWord w).hi < 64)
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true)
    (past : SailHistory cells pastEvents (NativeROM.state initial) before) :
    (Cell.ram (wordMemoryAddressWord w).toBitVec).read before = .ok (wordMemoryLoadWord w).toBitVec before := by
  have decoded := NativeWordMemoryDecoderProofs.decoded_fields fields query
  have mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus) := by simpa [load] using decoded.mask
  have shape := NativeWordMemoryShapeProofs.load_address holds mask
  have bound : (wordMemoryAddressWord w).value < 4194304 := by
    have low := shape.1.1
    dsimp [Word.value,limbBase] at *
    omega
  have index : (wordMemoryAddressWord w).value/4 < 1048576 := by omega
  have read := NativeWordMemoryHistoryProofs.constructed_rom_read_after_history kept past ⟨_,index⟩
  have address : BitVec.ofNat 32 (4*((wordMemoryAddressWord w).value/4)) = (wordMemoryAddressWord w).toBitVec := by
    have aligned : 4*((wordMemoryAddressWord w).value/4) = (wordMemoryAddressWord w).value := by
      have := shape.2.1
      omega
    exact congrArg (BitVec.ofNat 32) aligned
  rw [address] at read
  simpa only [wordMemoryLoadWord,if_pos inside] using read

/-- Both native load paths read the derived original pre-state. On ROM this
    follows constructed bytes/past frames; RAM uses the retained actual port. -/
theorem load_memory_read {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {cells : List Cell} (epoch : Nat) {initial before after : State} {pastEvents : List MemoryAccess}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (load : entry.data.family = false)
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true)
    (past : SailHistory cells pastEvents (NativeROM.state initial) before)
    (history : SailHistory cells ((NativeWordMemoryProjectedPortProofs.events epoch w).reverse.filter
      fun event => architecturalAddress event.2.1) before after) :
    (Cell.ram (wordMemoryAddressWord w).toBitVec).read before = .ok (wordMemoryLoadWord w).toBitVec before := by
  by_cases inside : (wordMemoryAddressWord w).hi < 64
  · exact rom_load_read holds fields query load inside kept past
  · have read := NativeWordMemoryProjectedPortProofs.ram_load_read epoch holds fields query load
      (Nat.le_of_not_gt inside) history
    simpa only [wordMemoryLoadWord,if_neg inside] using read

/-- All native retained reads/oldreads and the original architectural transfer
    are derived at one pre-state. No local source/value/result/state is supplied. -/
theorem transfer {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {cells : List Cell} (epoch : Nat) {initial before after : State} {pastEvents : List MemoryAccess}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true)
    (past : SailHistory cells pastEvents (NativeROM.state initial) before)
    (history : SailHistory cells ((NativeWordMemoryProjectedPortProofs.events epoch w).reverse.filter
      fun event => architecturalAddress event.2.1) before after) : WordMemoryTransfer w entry before after :=
  ⟨NativeWordMemoryProjectedPortProofs.retained_reads epoch holds fields query history,
    NativeWordMemoryProjectedPortProofs.source_read epoch holds fields query history,
    NativeWordMemoryProjectedPortProofs.destination_write epoch holds fields query history,
    fun load => ⟨load_memory_read epoch holds fields query load kept past history,
      load_register_write epoch holds fields query load history⟩,
    fun store => ⟨NativeWordMemoryProjectedPortProofs.store_second_read epoch holds fields query store history,
      store_memory_write epoch holds fields query store history⟩⟩

end Airbender.ReducedMachine.NativeWordMemoryTransferProofs
