import Airbender.Review.Trace.Families.ReducedMachine.UnifiedFetchedExecution

namespace Tests.NativeReducedUnifiedExecution
open Airbender ReducedMachine Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def add : UnifiedProgramEntry :=
  ⟨0,0x002081b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.ADD),
    ⟨.inl (.inr (.inl .add)),1,2,3,⟨0,0⟩,11,0⟩⟩
private def load : UnifiedProgramEntry :=
  ⟨0,0x0000a003,.LOAD (0,.Regidx 1,.Regidx 0,false,4),⟨.inr false,1,0,0,⟨0,0⟩,1025,2⟩⟩
private def branch : UnifiedProgramEntry :=
  ⟨0,0x00208263,.BTYPE (4,.Regidx 2,.Regidx 1,.BEQ),
    ⟨.inl (.inr (.inr (.inr (.inr (.inl .BEQ))))),1,2,0,⟨4,0⟩,70,0⟩⟩
private def jump : UnifiedProgramEntry :=
  ⟨0,0x004001ef,.JAL (4,.Regidx 3),
    ⟨.inl (.inr (.inr (.inr (.inr (.inr true))))),0,0,3,⟨4,0⟩,33025,0⟩⟩
private def indirect : UnifiedProgramEntry :=
  ⟨0,0x000081e7,.JALR (0,.Regidx 1,.Regidx 3),
    ⟨.inl (.inr (.inr (.inr (.inr (.inr false))))),1,0,3,⟨0,0⟩,257,0⟩⟩
private def one (entry : UnifiedProgramEntry) : SparseDecoderSetup UnifiedMode := ⟨[entry],1⟩
private def blank : State :=
  { (default : State) with regs := Std.ExtDHashMap.emptyWithCapacity, mem := Std.ExtHashMap.emptyWithCapacity }

/-- Constructor-sensitive input scopes do not impose memory/branch/JALR CSRs
    on ordinary original ADD programs, even with arbitrary initial reference state. -/
theorem ordinary_program_no_csrs (state : State) : UnifiedISA (one add) state := by
  constructor
  all_goals
    rintro ⟨entry,member,shape⟩
    have same : entry = add := by simpa [one,SparseDecoderSetup.program] using member
    subst entry
    simp [add,InstructionUsesMisa,InstructionUsesWordMemory] at shape

theorem ordinary_program_no_ram_domain (cells : List Cell) : UnifiedOrdinaryCells (one add) cells := by
  rintro ⟨entry,member,shape⟩
  have same : entry = add := by simpa [one,SparseDecoderSetup.program] using member
  subst entry
  simp [add,InstructionUsesWordMemory] at shape

/-- Successful branch/JAL reference configurations require only readable
    unrestricted misa, with no memory or indirect landing-pad security premise. -/
theorem branch_only_configuration {state : State} {value : BitVec 32}
    (read : state.regs.get? .misa = some value) : UnifiedISA (one branch) state := by
  constructor
  · intro _; exact ⟨value,read⟩
  all_goals
    rintro ⟨entry,member,shape⟩
    have same : entry = branch := by simpa [one,SparseDecoderSetup.program] using member
    subst entry
    simp [branch,InstructionUsesWordMemory] at shape

theorem jal_only_configuration {state : State} {value : BitVec 32}
    (read : state.regs.get? .misa = some value) : UnifiedISA (one jump) state := by
  constructor
  · intro _; exact ⟨value,read⟩
  all_goals
    rintro ⟨entry,member,shape⟩
    have same : entry = jump := by simpa [one,SparseDecoderSetup.program] using member
    subst entry
    simp [jump,InstructionUsesWordMemory] at shape

theorem jalr_missing_security_rejected {state : State}
    (missing : state.regs.get? .mseccfg = none) (bad : UnifiedISA (one indirect) state) : False := by
  obtain ⟨_,security,read,_⟩ := bad.indirect ⟨indirect,by simp [one,SparseDecoderSetup.program],_,rfl⟩
  rw [missing] at read
  cases read

theorem memory_missing_misa_rejected (bad : UnifiedISA (one load) blank) : False := by
  have config := bad.memory ⟨load,by simp [one,SparseDecoderSetup.program],by trivial⟩
  obtain ⟨value,read⟩ := config.isa
  simp [blank] at read

theorem memory_wrong_privilege_rejected {state : State}
    (wrong : state.regs.get? .cur_privilege = some .User) (bad : UnifiedISA (one load) state) : False := by
  have config := bad.memory ⟨load,by simp [one,SparseDecoderSetup.program],by trivial⟩
  have actual := config.privilege
  rw [wrong] at actual
  cases actual

theorem memory_clint_domain_rejected (bad : UnifiedOrdinaryCells (one load) [.ram 33554432]) : False := by
  have actual := bad ⟨load,by simp [one,SparseDecoderSetup.program],by trivial⟩ 33554432 (by simp)
  have rejected : ¬ OrdinaryWordAddress (33554432 : BitVec 32) := by unfold OrdinaryWordAddress; decide
  exact rejected actual

/-- A supported native row cannot lose a readonly or OLDREAD/write event in the
    common projection. This is conditional native evidence, not a NONEMPTY witness. -/
theorem supported_event_loss_rejected {w : Nat → ZMod mersenne31Modulus} {entry : SupportedProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : supportedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (epoch : Nat)
    (bad : ((rowEvents epoch (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily)).reverse.filter
      fun event => architecturalAddress event.2.1) ≠
      (rowEvents epoch (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily)).reverse) : False :=
  bad (NativeUnifiedExecutionProofs.supported_events native fields query epoch)

end Tests.NativeReducedUnifiedExecution
