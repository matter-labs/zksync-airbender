import Airbender.Review.Circuits.ReducedMachine.BodyPaddingTheorems
import Airbender.Review.Trace.Families.ReducedMachine.CSRCallers

namespace Airbender.Tests.NativeCSRPositive
open Arithmetic Trace ReducedMachine ReducedMachine.Native Verification
open Reference.RiscV.Sail Reference.Sail
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

def nativeRow (active : Bool) : Row mersenne31Modulus NativeReducedFamily :=
  ⟨.reduced,NativeCSRPositiveWitness.assignment active⟩

private def token (time : Nat) : MemoryToken mersenne31Modulus := ⟨0,(time,0),0⟩

def trace (active : Bool) : Data mersenne31Modulus NativeReducedFamily where
  rows := [nativeRow active]
  rom := NativeRuntimePool.table
  initial := PCState.boundary 0 (4,0)
  terminal := PCState.boundary 4 (8,0)
  initialMemory := [token 0]
  terminalMemory := [token 6]

private theorem state_ext (a b : PCState.State mersenne31Modulus)
    (pc : a.pc = b.pc) (timestamp : a.timestamp = b.timestamp) : a = b := by
  cases a
  cases b
  cases pc
  cases timestamp
  rfl

/-- All three x0 aliases retain OLDREADs and readonly timestamp refreshes. -/
theorem accepted : Accepted (runtimeCSRData (trace true)) := by
  constructor
  · intro row member
    have same : row = nativeRow true := by simpa [runtimeCSRData,trace] using member
    subst row
    exact NativeCSRPositiveWitness.body true
  · intro row member
    have same : row = nativeRow true := by simpa [runtimeCSRData,trace] using member
    subst row
    decide +kernel
  · change [(trace true).initial,(nativeRow true).finish].Perm
      [(trace true).terminal,(nativeRow true).start]
    have start : (nativeRow true).start = (trace true).initial := by
      apply state_ext <;> decide +kernel
    have finish : (nativeRow true).finish = (trace true).terminal := by
      apply state_ext <;> decide +kernel
    rw [start,finish]
    exact List.Perm.swap _ _ []
  · decide +kernel

/-- The active logical trace interface rejects execute0; it is not silently
    substituted for the full physical ordinary-row domain. -/
theorem inactive_logical_trace_rejected : ¬ Accepted (runtimeCSRData (trace false)) := by
  intro h
  have active := h.active (nativeRow false) (by simp [runtimeCSRData,trace])
  have inactive : (nativeRow false).assignment (nativeRow false).columns.execute = 0 := by decide +kernel
  rw [inactive] at active
  exact zero_ne_one active

-- Independent original public bytes, NOT the native eight-word ROM fixture.
def before : State :=
  { (default : State) with
    regs := (default : State).regs.insert .PC (0 : BitVec 32)
    mem := Std.ExtHashMap.emptyWithCapacity
      |>.insert 0 0x73 |>.insert 1 0x10 |>.insert 2 0x70 |>.insert 3 0x7c }

def entry : CSRProgramEntry :=
  ⟨0,0x7c701073,.CSRReg (1991,.Regidx 0,.Regidx 0,.CSRRW),(),0,0,0,⟨1991,0⟩,129,1⟩

def setup : SparseDecoderSetup CSRMode := ⟨[some entry],1⟩

private theorem public_word : (Cell.ram 0).read before = .ok (0x7c701073 : BitVec 32) before := by
  simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
    EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
    before,Std.ExtHashMap.getElem_insert]

private theorem csr_enabled : SailRV32.Functions.currentlyEnabled .Ext_Zicsr = .pure true := by
  rw [SailRV32.Functions.currentlyEnabled,SailRV32.Functions.hartSupports]
  rfl

private theorem original_decoder : SailRV32.Functions.encdec_backwards (0x7c701073 : BitVec 32) =
    .pure (.CSRReg (1991,.Regidx 0,.Regidx 0,.CSRRW)) := by
  dsimp only [SailRV32.Functions.encdec_backwards]
  rw [csr_enabled]
  rfl

theorem program_image : csrDecoderSetupImage before 1 1 = some setup := by
  have slot : programSlotRunWith csrDecoderFields before 0 = some (some entry) := by
    simp only [programSlotRunWith,public_word,original_decoder,bind,Option.bind,pure]
    rfl
  change (([0] : List (BitVec 32)).mapM (programSlotRunWith csrDecoderFields before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1)) = some setup
  simp only [List.mapM_cons,List.mapM_nil,slot,bind,Option.bind,pure]
  rfl

theorem public_inputs : ImageBoundary (runtimeCSRData (trace true)) before [.register 0] := by
  have zero : (Cell.register 0).read before = .ok (0 : BitVec 32) before := rfl
  have pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok (0 : BitVec 32) before := by
    apply read_register
    simp [before]
  constructor
  · decide
  · simp only [initialImage,List.mapM_cons,List.mapM_nil,zero]
    rfl
  · rw [initialState,pc]
    rfl

theorem decoded : CSRDecodedTrace (trace true) setup := by
  intro row member
  have same : row = nativeRow true := by simpa [trace] using member
  subst row
  refine ⟨⟨0,by decide⟩,?_⟩
  decide +kernel

/-- Complete nonempty initialized GPR/source/request/caller observations;
    no original CSR clause, delegated worker or native8wordROM execution claim. -/
theorem initialized_callers : CSRRequestHistory (runtimeCSRData (trace true)) setup before [.register 0] ∧
    ∃ callers, CSRCallerProjection (runtimeCSRData (trace true)) callers :=
  public_runtime_csr_callers program_image public_inputs accepted decoded
    (by intro cell member; simp only [List.mem_cons,List.mem_nil_iff,or_false] at member; subst cell; trivial)

theorem actual_request : csrRequest (nativeRow true).assignment = ⟨1,1991,some 0,3⟩ :=
  (NativeCSRBodyPaddingProofs.observations true).2

theorem actual_caller_clock : (csrCallerObservation (nativeRow true)).clock = 7 := by decide +kernel

theorem inactive_body_still_requests :
    FlatOperation.ConstraintsHoldFlat (environment (nativeRow false).assignment) (importedConstraints NativeRuntimePool.table) ∧
    (nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
    csrRequest (nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  ⟨NativeCSRPositiveWitness.body false,NativeCSRBodyPaddingProofs.observations false⟩

private def corruptedAssignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 92 then 0 else NativeCSRPositiveWitness.assignment true i

private theorem corrupted_fields : corruptedAssignment 12 = (csrMask : ZMod mersenne31Modulus) ∧
    corruptedAssignment 92 = 0 ∧ corruptedAssignment 65 = 1 := by decide +kernel

private theorem corrupted_rejected_at {setupTable : Table (ZMod mersenne31Modulus) (fields 4)} :
    ¬ FlatOperation.ConstraintsHoldFlat (environment corruptedAssignment) (importedConstraints setupTable) := by
  intro forged
  have equal := (NativeCSRFieldProofs.request_equations forged corrupted_fields.1).2.1
  rw [corrupted_fields.2.1,corrupted_fields.2.2] at equal
  exact zero_ne_one equal

/-- The actual imported request coordinate is checked against the unchanged
    generic native equations BEFORE instantiating the large runtime pool. -/
theorem corrupted_request_rejected : ¬ FlatOperation.ConstraintsHoldFlat
    (environment corruptedAssignment) (importedConstraints NativeRuntimePool.table) :=
  corrupted_rejected_at

end Airbender.Tests.NativeCSRPositive
