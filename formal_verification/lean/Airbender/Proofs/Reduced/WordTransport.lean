import Airbender.Proofs.Reduced.ControlExecution
import Airbender.Proofs.Trace.PooledMemory

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

private theorem canonical_ram_cell {p : Nat} {cells : List Cell}
    {w : Nat → ZMod p} {port : MemoryPort}
    (located : ∃ cell ∈ cells, port.address.code w = cell.addressCode)
    (ram : ∃ code, port.address.code w = Nat.pair 1 code) :
    Cell.ram (port.address.word w).toBitVec ∈ cells ∧
      port.address.code w = (Cell.ram (port.address.word w).toBitVec).addressCode := by
  obtain ⟨cell, belongs, equal⟩ := located
  cases cell with
  | register index =>
    obtain ⟨code, actual⟩ := ram
    have impossible := actual.symm.trans equal
    simp [Cell.addressCode, Nat.pair_eq_pair] at impossible
  | ram address =>
    have same : (port.address.word w).toBitVec = address :=
      (congrArg Word.toBitVec (address_word equal)).trans (Word.ofBitVec_roundtrip address)
    rw [same]
    exact ⟨belongs, equal⟩

/-- Shared initialized locations and native arithmetic determine each LW/SW address. -/
theorem word_address_from_shared_history
    (hp : FieldCapacity.NativeWordCapacity babyBearModulus)
    (inverse : SerializedInverse.Clock babyBearModulus)
    {w : Nat → ZMod babyBearModulus} {cells : List Cell}
    {setup : Table (ZMod babyBearModulus) (fields 9)}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (WordMemory.importedConstraints setup))
    (source : (readToken w WordMemory.importedConstraintsMemoryPorts[0]).word.Bounded)
    (addresses : ∀ port ∈ WordMemory.importedConstraintsMemoryPorts,
      ∃ cell ∈ cells, port.address.code w = cell.addressCode)
    {initial : State} {entry : PooledProgramEntry}
    (sourceEntry : entry.SourceWith initial AddSub.Modular.External.decoderFields)
    (family : entry.data.family = .wordMemory)
    (query : (⟨.wordMemory, w⟩ : Row babyBearModulus PooledFamily).decoderQuery = entry.query)
    (store : Bool) (selected : w 10 = if store then 1 else 0) :
    let address := Word.mk (w (if store then 25 else 19)).val (w (if store then 26 else 20)).val
    address.Bounded ∧ address.toBitVec = (Word.mk (w 17).val (w 18).val).toBitVec +
      (Word.mk (w 8).val (w 9).val).toBitVec ∧ Cell.ram address.toBitVec ∈ cells := by
  have addressBounds (port : MemoryPort) (present : port ∈ WordMemory.importedConstraintsMemoryPorts) :
      (port.address.word w).Bounded := by
    obtain ⟨cell, _, same⟩ := addresses port present
    rw [address_word same]
    exact cell_address_bound cell
  have ramCell (port : MemoryPort) (present : port ∈ WordMemory.importedConstraintsMemoryPorts)
      (ram : ∃ code, port.address.code w = Nat.pair 1 code) :=
    canonical_ram_cell (addresses port present) ram
  have clockSize : 2 * timestampBase + 4 < babyBearModulus := by dsimp [timestampBase]; omega
  have limbSize : limbBase < babyBearModulus := by dsimp [limbBase]; omega
  have oneValue : (1 : ZMod babyBearModulus).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by decide : 1 < babyBearModulus)
  have sourceBound : (Word.mk (w 17).val (w 18).val).Bounded := by
    simpa [read_word, WordMemory.importedConstraintsMemoryPorts] using source
  have fetched := sourceEntry
  have immediateBound : (Word.mk (w 8).val (w 9).val).Bounded := by
    obtain original | original | original | original | original := AddSub.Modular.External.Proofs.source_cases fetched
    all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
    all_goals subst entry
    · rw [mapped_query] at query
      change (⟨.wordMemory, w⟩ : Row babyBearModulus).decoderQuery = originalEntry.query at query
      have mode : originalEntry.data.family = .wordMemory := by
        cases mode : originalEntry.data.family
        · simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
        · rfl
      exact query_immediate limbSize (row := (⟨.wordMemory, w⟩ : Row babyBearModulus))
        (AddSub.Modular.External.Proofs.memory_fields originalSource.fields mode) query
    · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
    · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
    · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
    · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  cases store
  all_goals dsimp only [Bool.false_eq_true, if_false, if_true] at selected ⊢
  · have portMember : WordMemory.importedConstraintsMemoryPorts[1] ∈
        (⟨.wordMemory, w⟩ : Row babyBearModulus PooledFamily).ports := by
      change WordMemory.importedConstraintsMemoryPorts[1] ∈ WordMemory.importedConstraintsMemoryPorts
      simp [WordMemory.importedConstraintsMemoryPorts]
    have bound := addressBounds _ (by simpa only [Trace.Row.ports, CircuitLayout.ports] using portMember)
    have cell := ramCell _ (by simpa only [Trace.Row.ports, CircuitLayout.ports] using portMember)
      (by refine ⟨Nat.pair (w 19).val (w 20).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue])
    exact local_word_address (by dsimp [ROM.limit]; omega) inverse core false selected
      sourceBound immediateBound bound cell.1
  · have portMember : WordMemory.importedConstraintsMemoryPorts[2] ∈
        (⟨.wordMemory, w⟩ : Row babyBearModulus PooledFamily).ports := by
      change WordMemory.importedConstraintsMemoryPorts[2] ∈ WordMemory.importedConstraintsMemoryPorts
      simp [WordMemory.importedConstraintsMemoryPorts]
    have bound := addressBounds _ (by simpa only [Trace.Row.ports, CircuitLayout.ports] using portMember)
    have cell := ramCell _ (by simpa only [Trace.Row.ports, CircuitLayout.ports] using portMember)
      (by refine ⟨Nat.pair (w 25).val (w 26).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue])
    exact local_word_address (by dsimp [ROM.limit]; omega) inverse core true selected
      sourceBound immediateBound bound cell.1

/-- Actual row histories realize native word reads and writes at initialized addresses. -/
theorem word_transport_from_shared_history
    {w : Nat → ZMod babyBearModulus} {cells : List Cell}
    (addresses : ∀ port ∈ WordMemory.importedConstraintsMemoryPorts,
      ∃ cell ∈ cells, port.address.code w = cell.addressCode)
    (store : Bool) (selected : w 10 = if store then 1 else 0)
    {before after : State} (epoch : Nat)
    (history : SailHistory cells (rowEvents epoch (⟨.wordMemory, w⟩ : Row babyBearModulus PooledFamily)).reverse before after) :
    if store then
      run (writeMemory (size := 4) (Word.mk (w 25).val (w 26).val).toBitVec
        (Word.mk (w 31).val (w 32).val).toBitVec) before = .ok () after
    else
      (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4
        (Word.mk (w 19).val (w 20).val).toBitVec.toNat).run before =
        .ok (Word.mk (w 23).val (w 24).val).toBitVec before := by
  have oneValue : (1 : ZMod babyBearModulus).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by decide : 1 < babyBearModulus)
  cases store
  · simp only [Bool.false_eq_true, if_false] at selected ⊢
    have present : WordMemory.importedConstraintsMemoryPorts[1] ∈
        (⟨.wordMemory, w⟩ : Row babyBearModulus PooledFamily).ports := by
      change WordMemory.importedConstraintsMemoryPorts[1] ∈ WordMemory.importedConstraintsMemoryPorts
      simp [WordMemory.importedConstraintsMemoryPorts]
    have cell := canonical_ram_cell (addresses _ (by simpa only [Trace.Row.ports, CircuitLayout.ports] using present))
      (by refine ⟨Nat.pair (w 19).val (w 20).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue])
    have read := native_history_read epoch rfl rfl rfl history present cell.2
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord, MemoryAddress.word, Cell.read] using read
  · simp only [if_true] at selected ⊢
    have present : WordMemory.importedConstraintsMemoryPorts[2] ∈
        (⟨.wordMemory, w⟩ : Row babyBearModulus PooledFamily).ports := by
      change WordMemory.importedConstraintsMemoryPorts[2] ∈ WordMemory.importedConstraintsMemoryPorts
      simp [WordMemory.importedConstraintsMemoryPorts]
    have cell := canonical_ram_cell (addresses _ (by simpa only [Trace.Row.ports, CircuitLayout.ports] using present))
      (by refine ⟨Nat.pair (w 25).val (w 26).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue])
    have written := native_history_write epoch rfl rfl rfl history rfl cell.2
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord, MemoryAddress.word, Cell.write] using written

end Airbender.AddSub.Modular.External.Caller.Proofs
