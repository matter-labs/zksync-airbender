import Airbender.Review.Trace.Families.ReducedMachine.WordMemoryTransfers

namespace Tests.NativeReducedWordMemoryTransfers
open Airbender ReducedMachine Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

section Local
variable {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
  {cells : List Cell} (epoch : Nat) {before after : State}
  (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
  (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
  (query : decoderQuery w = entry.query)
  (history : SailHistory cells ((NativeWordMemoryProjectedPortProofs.events epoch w).reverse.filter
    fun event => architecturalAddress event.2.1) before after)

include epoch holds fields query history

/-- Aliased load source/destination OLDREADs agree BEFORE the actual write. -/
theorem load_alias_reads_before_write (load : entry.data.family = false)
    (aliasing : entry.data.rd = entry.data.rs1) :
    (sourceWord w).toBitVec = memoryWord (importedConstraintsMemoryPorts[2].readCode w) := by
  have source := NativeWordMemoryProjectedPortProofs.source_read epoch holds fields query history
  have old := NativeWordMemoryProjectedPortProofs.retained_reads epoch holds fields query history 2
    (by simp [wordMemoryPortDomains])
  have oldRead : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok (memoryWord (importedConstraintsMemoryPorts[2].readCode w)) before := by
    simpa [wordMemoryPortCells,load,Cell.read,aliasing] using old
  exact (EStateM.Result.ok.inj (source.symm.trans oldRead)).1

/-- SW keeps both original source observations in one pre-state, including aliases. -/
theorem store_source_alias_reads (store : entry.data.family = true)
    (aliasing : entry.data.rs2 = entry.data.rs1) :
    (sourceWord w).toBitVec = (wordMemorySecondWord w).toBitVec := by
  have source := NativeWordMemoryProjectedPortProofs.source_read epoch holds fields query history
  have second := NativeWordMemoryProjectedPortProofs.store_second_read epoch holds fields query store history
  rw [aliasing] at second
  exact (EStateM.Result.ok.inj (source.symm.trans second)).1

/-- Dummy decoded rd0 does not turn a changing SW into a data stutter. -/
theorem changing_store_cannot_stutter (store : entry.data.family = true)
    (changed : memoryWord (importedConstraintsMemoryPorts[2].readCode w) ≠ (wordMemorySecondWord w).toBitVec)
    (stutter : after = before) : False := by
  have old := NativeWordMemoryProjectedPortProofs.retained_reads epoch holds fields query history 2
    (by simp [wordMemoryPortDomains])
  have oldRead : (Cell.ram (wordMemoryAddressWord w).toBitVec).read before =
      .ok (memoryWord (importedConstraintsMemoryPorts[2].readCode w)) before := by
    simpa [wordMemoryPortCells,store] using old
  have write := NativeWordMemoryTransferProofs.store_memory_write epoch holds fields query store history
  have canonical := write_word_state before (wordMemoryAddressWord w).toBitVec (wordMemorySecondWord w).toBitVec
  have same := (EStateM.Result.ok.inj (canonical.symm.trans write)).2
  have read : (Cell.ram (wordMemoryAddressWord w).toBitVec).read after =
      .ok (wordMemorySecondWord w).toBitVec after := by
    rw [← same]
    exact written_word_read before (wordMemoryAddressWord w).toBitVec.toNat (wordMemorySecondWord w).toBitVec
  rw [stutter] at read
  exact changed (EStateM.Result.ok.inj (oldRead.symm.trans read)).1

/-- Discarding the loaded value uses the ORIGINAL unmasked x0 accessor. -/
theorem native_load_x0_stutters (load : entry.data.family = false) (zero : entry.data.rd = 0) :
    after = before := by
  have actual := NativeWordMemoryTransferProofs.load_register_write epoch holds fields query load history
  rw [zero] at actual
  exact (EStateM.Result.ok.inj
    ((NativeWordMemoryTransferProofs.zero_register_write before (wordMemoryLoadWord w).toBitVec).symm.trans actual)).2.symm

end Local

/-- A positive original nonzero load-value write to x0 still discards the value. -/
theorem original_x0_discards_unmasked_rom (before : State) :
    run (SailRV32.Functions.wX_bits (.Regidx 0) (21015 : BitVec 32)) before = .ok () before :=
  NativeWordMemoryTransferProofs.zero_register_write before _

/-- Even load-to-x0 cannot bypass its architectural memory read. -/
theorem discarded_load_read_cannot_fail {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {cells : List Cell} (epoch : Nat) {initial before after : State} {pastEvents : List MemoryAccess}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (load : entry.data.family = false)
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true)
    (past : SailHistory cells pastEvents (NativeROM.state initial) before)
    (history : SailHistory cells ((NativeWordMemoryProjectedPortProofs.events epoch w).reverse.filter
      fun event => architecturalAddress event.2.1) before after)
    (bad : (Cell.ram (wordMemoryAddressWord w).toBitVec).read before =
      .error (.OutOfMemoryRange (wordMemoryAddressWord w).value) before) : False := by
  have actual := NativeWordMemoryTransferProofs.load_memory_read epoch holds fields query load kept past history
  rw [actual] at bad
  cases bad

/-- The actual ROM read is independent of ignored shadow read37/38. -/
theorem rom_read_ignores_shadow {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {cells : List Cell} {initial before : State} {pastEvents : List MemoryAccess}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (load : entry.data.family = false)
    (address : wordMemoryAddressWord w = ⟨16,0⟩)
    (kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true)
    (past : SailHistory cells pastEvents (NativeROM.state initial) before) :
    (Cell.ram 16).read before = .ok (21015 : BitVec 32) before := by
  have actual := NativeWordMemoryTransferProofs.rom_load_read holds fields query load
    (by rw [address]; decide) kept past
  rw [address] at actual
  simpa [wordMemoryLoadWord,address,wordMemoryROMWord,NativeFixed.wordROMValue,Word.toBitVec,Word.value,limbBase] using actual

private def base : State :=
  { (default : State) with
    regs := Std.ExtDHashMap.emptyWithCapacity.insert .PC (0 : BitVec 32)
    mem := Std.ExtHashMap.emptyWithCapacity }
private def initial : State := NativeROM.state base
private def seeds : List ShadowSeed := [(16,123)]
private def trace : Data mersenne31Modulus NativeReducedFamily where
  rows := []
  rom := NativeFixed.table
  initial := PCState.boundary 0 (4,0)
  terminal := PCState.boundary 0 (4,0)
  initialMemory := shadowTokens seeds
  terminalMemory := shadowTokens seeds
private def setup : SparseDecoderSetup WordMemoryMode := ⟨[],1⟩
private theorem inputs : ShadowImageBoundary (fixedData trace) initial [] seeds := by
  constructor
  · decide
  · intro cell member; cases member
  · intro seed member
    have same : seed = ((16 : BitVec 32),(123 : BitVec 32)) := by simpa [seeds] using member
    subst seed
    decide
  · rfl
  · have read : run (SailRV32.Functions.get_arch_pc ()) initial = .ok (0 : BitVec 32) initial := by
      apply read_register
      change (NativeROM.state base).regs.get? .PC = some (0 : BitVec 32)
      rw [NativeROMProofs.registers]
      simp [base]
    change initialState initial (4,0) = some (PCState.boundary 0 (4,0))
    simp only [initialState,read]
private theorem accepted : Accepted (fixedData trace) := by
  constructor
  · intro row present; simp [fixedData,trace] at present
  · intro row present; simp [fixedData,trace] at present
  · exact List.Perm.refl _
  · exact List.Perm.refl _
private theorem decoded : WordMemoryDecodedTrace (fixedData trace) setup := by
  intro row present; simp [fixedData,trace] at present

/-- Complete actual-native EMPTY transfer scope with exact constructed bytes,
    independent shadow123, and no CSR or per-row architectural read premise.
    The conditional local tests above are not full117-equation nonempty witnesses. -/
theorem empty_transfers_without_csrs : WordMemoryTransferHistory (fixedData trace) setup initial [] :=
  public_word_memory_transfers (count := 0) (logCapacity := 0) rfl
    inputs accepted decoded (by intro cell member; cases member) (by decide)

end Tests.NativeReducedWordMemoryTransfers
