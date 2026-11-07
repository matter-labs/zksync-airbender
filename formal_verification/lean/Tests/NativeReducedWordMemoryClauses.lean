import Airbender.Review.Trace.Families.ReducedMachine.WordMemoryClauses

namespace Tests.NativeReducedWordMemoryClauses
open Airbender ReducedMachine Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def entry : WordMemoryProgramEntry :=
  ⟨0,0x0000a003,.LOAD (0,.Regidx 1,.Regidx 0,false,4),⟨false,1,0,0,⟨0,0⟩,1025,2⟩⟩
private def nonempty : SparseDecoderSetup WordMemoryMode := ⟨[entry],1⟩
private def blank : State :=
  { (default : State) with regs := Std.ExtDHashMap.emptyWithCapacity, mem := Std.ExtHashMap.emptyWithCapacity }

/-- Empty original public programs do not acquire memory CSR requirements. -/
theorem empty_program_no_csrs (state : State) : WordMemoryISA ⟨[],1⟩ state := by
  intro bad
  exact False.elim (bad rfl)

/-- A present memory program cannot fabricate readable misa. -/
theorem missing_misa_rejected (bad : WordMemoryISA nonempty blank) : False := by
  obtain ⟨value,read⟩ := (bad (by simp [nonempty,SparseDecoderSetup.program])).isa
  simp [blank] at read

/-- Initial privilege is reference input, not an inferred native answer. -/
theorem wrong_privilege_rejected {state : State}
    (wrong : state.regs.get? .cur_privilege = some .User)
    (bad : WordMemoryISA nonempty state) : False := by
  have actual := (bad (by simp [nonempty,SparseDecoderSetup.program])).privilege
  rw [wrong] at actual
  cases actual

theorem clint_domain_rejected (bad : WordMemoryOrdinaryCells [.ram 33554432]) : False := by
  have actual := bad 33554432 (by simp)
  have rejected : ¬ OrdinaryWordAddress (33554432 : BitVec 32) := by unfold OrdinaryWordAddress; decide
  exact rejected actual

theorem signature_domain_rejected (bad : WordMemoryOrdinaryCells [.ram 201326592]) : False := by
  have actual := bad 201326592 (by simp)
  have rejected : ¬ OrdinaryWordAddress (201326592 : BitVec 32) := by unfold OrdinaryWordAddress; decide
  exact rejected actual

/-- Independent pinned-platform boundaries include top aligned RV32 memory. -/
theorem ordinary_boundary_matrix : OrdinaryWordAddress (0 : BitVec 32) ∧
    OrdinaryWordAddress (4194300 : BitVec 32) ∧ OrdinaryWordAddress (33603584 : BitVec 32) ∧
    OrdinaryWordAddress (201326624 : BitVec 32) ∧ OrdinaryWordAddress (0xfffffffc : BitVec 32) := by
  unfold OrdinaryWordAddress
  decide

private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }
private def configured (isa address : BitVec 32) : State :=
  { (default : State) with
    regs := ((Std.ExtDHashMap.emptyWithCapacity : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 address |>.insert .x2 (123 : BitVec 32)
      |>.insert .mstatus 0 |>.insert .cur_privilege .Machine |>.insert .misa isa
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
      |>.insert .pmpcfg_n (Vector.replicate 64 0) |>.insert .pmpaddr_n (Vector.replicate 64 0)
      |>.insert .pma_regions [rv32Region attributes] |>.insert .mhartid 7 |>.insert .htif_tohost_base none)
    mem := Std.ExtHashMap.emptyWithCapacity }
private theorem configured_privilege (isa address : BitVec 32) :
    (configured isa address).regs.get? .cur_privilege = some .Machine := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_status (isa address : BitVec 32) :
    (configured isa address).regs.get? .mstatus = some 0 := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_isa (isa address : BitVec 32) :
    (configured isa address).regs.get? .misa = some isa := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_supervisor (isa address : BitVec 32) :
    (configured isa address).regs.get? .senvcfg = some 0 := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_machine (isa address : BitVec 32) :
    (configured isa address).regs.get? .menvcfg = some 0x10 := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_pmp (isa address : BitVec 32) :
    (configured isa address).regs.get? .pmpcfg_n = some (Vector.replicate 64 0) := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_pmpAddresses (isa address : BitVec 32) :
    (configured isa address).regs.get? .pmpaddr_n = some (Vector.replicate 64 0) := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_pma (isa address : BitVec 32) :
    (configured isa address).regs.get? .pma_regions = some [rv32Region attributes] := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_hart (isa address : BitVec 32) :
    (configured isa address).regs.get? .mhartid = some 7 := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_htif (isa address : BitVec 32) :
    (configured isa address).regs.get? .htif_tohost_base = some none := by
  simp [configured]
  rfl

private theorem configuration (isa address : BitVec 32) : FlatMemoryConfiguration (configured isa address) :=
  ⟨configured_privilege isa address,configured_status isa address,⟨isa,configured_isa isa address⟩,
    ⟨0,configured_supervisor isa address⟩,⟨0x10,configured_machine isa address⟩,
    configured_pmp isa address,⟨Vector.replicate 64 0,configured_pmpAddresses isa address⟩,
    ⟨attributes,configured_pma isa address,rfl,rfl,rfl⟩,⟨7,configured_hart isa address⟩,configured_htif isa address⟩

/-- Positive retained original LW-to-x0 reads actual constructed ROM21015 and
    discards its unmasked result. misa value is unrestricted reference data.
    This is ORIGINAL Sail execution, not a full117-equation native witness. -/
theorem original_rom_load_x0 [MemoryPlatform SailRV32.exception] (isa : BitVec 32) :
    run (SailRV32.Functions.execute_LOAD 0 (.Regidx 1) (.Regidx 0) false 4)
      (NativeROM.state (configured isa 16)) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (NativeROM.state (configured isa 16)) := by
  let before := NativeROM.state (configured isa 16)
  have config : FlatMemoryConfiguration before :=
    configuration_register_frame (NativeROMProofs.registers _) (configuration isa 16)
  have source : run (SailRV32.Functions.rX_bits (.Regidx 1)) before = .ok (16 : BitVec 32) before := by
    apply read_register
    change (NativeROM.state (configured isa 16)).regs.get? .x1 = some (16 : BitVec 32)
    rw [NativeROMProofs.registers]
    simp [configured,Std.ExtDHashMap.get?_insert]
  have memory : (Cell.ram 16).read before = .ok (21015 : BitVec 32) before := by
    have actual := NativeROMProofs.numerical_read (configured isa 16) ⟨4,by decide⟩
    simpa [wordMemoryROMWord,NativeFixed.wordROMValue,Word.toBitVec,Word.value,limbBase,before] using actual
  have read := virtual_word_read config (.Regidx 1) (0 : BitVec 32) source
    (by decide) (by unfold OrdinaryWordAddress; decide) memory
  have offset : SailRV32.Functions.sign_extend (m := 32) (0 : BitVec 12) = (0 : BitVec 32) := by decide
  rw [← offset] at read
  rw [load_word read,run_bind_of_ok _ _ _ _ _ (NativeWordMemoryTransferProofs.zero_register_write before 21015)]
  rfl

/-- Positive original SW copies rs2 to RAM through retained virtual memory.
    It neither writes nor discards a dummy architectural rd0. -/
theorem original_ram_store [MemoryPlatform SailRV32.exception] (isa : BitVec 32) :
    run (SailRV32.Functions.execute_STORE 0 (.Regidx 2) (.Regidx 1) 4) (configured isa 4194304) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (wordWriteState (configured isa 4194304) 4194304 123) := by
  have first : run (SailRV32.Functions.rX_bits (.Regidx 1)) (configured isa 4194304) =
      .ok (4194304 : BitVec 32) (configured isa 4194304) := by
    apply read_register; simp [configured,Std.ExtDHashMap.get?_insert]
  have second : run (SailRV32.Functions.rX_bits (.Regidx 2)) (configured isa 4194304) =
      .ok (123 : BitVec 32) (configured isa 4194304) := by
    apply read_register; simp [configured,Std.ExtDHashMap.get?_insert]
  have write := virtual_word_write (configuration isa 4194304) (.Regidx 1) (0 : BitVec 32) first
    (by decide) (by unfold OrdinaryWordAddress; decide) (123 : BitVec 32)
  have offset : SailRV32.Functions.sign_extend (m := 32) (0 : BitVec 12) = (0 : BitVec 32) := by decide
  rw [← offset] at write
  exact store_word second write

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

/-- Complete EMPTY actual-native public clause scope has no CSR premise,
    retains independent shadow123, and uses the exact native ROM byte constructor. -/
theorem empty_clauses_without_csrs [MemoryPlatform SailRV32.exception] :
    WordMemoryClauseHistory (fixedData trace) setup initial [] :=
  public_word_memory_clauses (count := 0) (logCapacity := 0) rfl
    inputs accepted decoded (by intro cell member; cases member) (by decide)
    (empty_program_no_csrs _) (by intro address member; cases member)

end Tests.NativeReducedWordMemoryClauses
