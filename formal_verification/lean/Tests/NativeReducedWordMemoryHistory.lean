import Airbender.Review.Trace.Families.ReducedMachine.WordMemoryHistory
import Airbender.Review.Trace.Families.ReducedMachine.WordMemoryAddressDomains

namespace Tests.NativeReducedWordMemoryHistory
open Airbender ReducedMachine Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Even source x0 is a retained actual port; projection is by address space. -/
theorem source_cannot_be_filtered {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (bad : architecturalAddress (importedConstraintsMemoryPorts[0].address.code w) = false) : False := by
  have actual := NativeWordMemoryDomainProofs.port_domains holds fields query 0
  simp [wordMemoryPortDomains,bad] at actual

theorem store_memory_cannot_be_filtered {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (bad : architecturalAddress (importedConstraintsMemoryPorts[2].address.code w) = false) : False := by
  have actual := NativeWordMemoryDomainProofs.port_domains holds fields query 2
  simp [wordMemoryPortDomains,bad] at actual

theorem rom_shadow_must_be_filtered {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (load : entry.data.family = false) (inside : (wordMemoryAddressWord w).hi < 64)
    (bad : architecturalAddress (importedConstraintsMemoryPorts[1].address.code w) = true) : False := by
  have actual := NativeWordMemoryDomainProofs.port_domains holds fields query 1
  simp [wordMemoryPortDomains,load,bad,Nat.not_le_of_gt inside] at actual

theorem ram_refresh_cannot_be_filtered {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (load : entry.data.family = false) (ram : 64 ≤ (wordMemoryAddressWord w).hi)
    (bad : architecturalAddress (importedConstraintsMemoryPorts[1].address.code w) = false) : False := by
  have actual := NativeWordMemoryDomainProofs.port_domains holds fields query 1
  simp [wordMemoryPortDomains,load,bad,ram] at actual

/-- An ignored ROM shadow still needs its actual native matching seed. -/
theorem missing_shadow_seed_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells [])
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (inside : (wordMemoryAddressWord row.assignment).hi < 64) : False := by
  obtain ⟨seed,member,_⟩ := (public_word_memory_address_domains image inputs accepted decoded row present).2 inside
  cases member

theorem missing_ram_cell_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (ram : 64 ≤ (wordMemoryAddressWord row.assignment).hi)
    (missing : Cell.ram (wordMemoryAddressWord row.assignment).toBitVec ∉ cells) : False :=
  missing ((public_word_memory_address_domains image inputs accepted decoded row present).1 ram)

theorem nonzero_x0_event_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    {event : MemoryAccess} (present : event ∈ (fixedData trace).nativeEvents)
    (address : event.2.1 = (Cell.register 0).addressCode) (bad : memoryWord event.2.2.2 ≠ 0) : False :=
  bad (NativeShadowHistoryProofs.shadow_zero_writes image inputs accepted decoded event present address)

/-- Capacity is derived for every full public instruction window. -/
theorem public_code_window {initial : State} {count logCapacity : Nat} {setup : SparseDecoderSetup WordMemoryMode}
    (image : wordMemoryDecoderSetupImage initial count logCapacity = some setup)
    (capacity : count ≤ 1048576) {entry : WordMemoryProgramEntry} (present : entry ∈ setup.program) :
    entry.pc.toNat+4 ≤ 4194304 := NativeWordMemoryHistoryProofs.setup_rom_pc image capacity present

private def before : State := wordWriteState
  { (default : State) with mem := Std.ExtHashMap.emptyWithCapacity |>.insert 0 (0x83 : BitVec 8) }
  4194304 (1 : BitVec 32)
private def after : State := wordWriteState before 4194304 (123 : BitVec 32)
private def cells : List Cell := [.ram 4194304]
private def event : MemoryAccess := (5,(Cell.ram 4194304).addressCode,Nat.pair 1 0,Nat.pair 123 0)
private theorem history : SailHistory cells [event] before after := by
  refine SailHistory.cons (SailHistory.nil before) (.ram 4194304) (by simp [cells]) rfl ?_ ?_
  · have code : memoryWord (Nat.pair 1 0) = (1 : BitVec 32) := by
      simp [memoryWord,Nat.unpair_pair,Word.toBitVec,Word.value]
    change (Cell.ram 4194304).read before = .ok (memoryWord (Nat.pair 1 0)) before
    rw [code]
    exact written_word_read
      { (default : State) with mem := Std.ExtHashMap.emptyWithCapacity |>.insert 0 (0x83 : BitVec 8) }
      4194304 1
  · have code : memoryWord (Nat.pair 123 0) = (123 : BitVec 32) := by
      simp [memoryWord,Nat.unpair_pair,Word.toBitVec,Word.value]
    change Reference.Sail.run ((Cell.ram 4194304).write (memoryWord (Nat.pair 123 0))) before = .ok () after
    rw [code]
    exact write_word_state before 4194304 123

/-- A positive ORIGINAL Sail RAM write changes data and preserves a real ROM
    code byte. This is not a full native117-equation accepted SW witness. -/
theorem original_ram_write_preserves_code :
    after.mem[0]? = some (0x83 : BitVec 8) ∧
    (Cell.ram 4194304).read after = .ok (123 : BitVec 32) after := by
  have kept : ∀ cell ∈ cells, architecturalAddress cell.addressCode = true := by
    intro cell member
    have same : cell = .ram 4194304 := by simpa [cells] using member
    subst cell
    rw [NativeShadowProofs.architectural_ram]
    decide
  have frame := NativeWordMemoryHistoryProofs.projected_history_rom_bytes kept history 0 (by decide)
  refine ⟨?_,written_word_read before 4194304 123⟩
  rw [frame]
  simp [before,wordWriteState,Std.ExtHashMap.getElem_insert]

private def emptyBefore : State :=
  { (default : State) with
    regs := Std.ExtDHashMap.emptyWithCapacity.insert .PC (0 : BitVec 32)
    mem := Std.ExtHashMap.emptyWithCapacity }
private def emptySeeds : List ShadowSeed := [(16,123)]
private def emptyTrace : Data mersenne31Modulus NativeReducedFamily where
  rows := []
  rom := NativeFixed.table
  initial := PCState.boundary 0 (4,0)
  terminal := PCState.boundary 0 (4,0)
  initialMemory := shadowTokens emptySeeds
  terminalMemory := shadowTokens emptySeeds
private def emptySetup : SparseDecoderSetup WordMemoryMode := ⟨[],1⟩
private theorem emptyInputs : ShadowImageBoundary (fixedData emptyTrace) emptyBefore [] emptySeeds := by
  constructor
  · decide
  · intro cell member; cases member
  · intro seed member
    have same : seed = ((16 : BitVec 32),(123 : BitVec 32)) := by simpa [emptySeeds] using member
    subst seed
    decide
  · rfl
  · have read : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) emptyBefore =
        .ok (0 : BitVec 32) emptyBefore := by
      apply read_register
      simp [emptyBefore]
    change initialState emptyBefore (4,0) = some (PCState.boundary 0 (4,0))
    simp only [initialState,read]
private theorem emptyAccepted : Accepted (fixedData emptyTrace) := by
  constructor
  · intro row present; simp [fixedData,emptyTrace] at present
  · intro row present; simp [fixedData,emptyTrace] at present
  · exact List.Perm.refl _
  · exact List.Perm.refl _
private theorem emptyDecoded : WordMemoryDecodedTrace (fixedData emptyTrace) emptySetup := by
  intro row present; simp [fixedData,emptyTrace] at present

/-- Full new public history scope succeeds on an actual native empty trace
    with independent shadow123 and no initial CSR or architectural byte reads. -/
theorem empty_history_without_csrs : WordMemoryProjectedHistory (fixedData emptyTrace) emptySetup emptyBefore [] :=
  public_word_memory_shadow_history (count := 0) (logCapacity := 0) rfl
    emptyInputs emptyAccepted emptyDecoded (by intro cell member; cases member) (by decide)

end Tests.NativeReducedWordMemoryHistory
