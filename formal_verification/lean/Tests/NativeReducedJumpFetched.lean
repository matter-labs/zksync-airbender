import Airbender.Review.Trace.Families.ReducedMachine.JumpFetchedExecution

namespace Tests.NativeReducedJumpFetched
open Airbender Arithmetic Trace ReducedMachine Native
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Empty rows still bind the actual native/public PC and initial clock. No
    instruction row or complete positive117-equation row is claimed here. -/
private def before (pc : BitVec 32) : State :=
  { (default : State) with regs := Std.ExtDHashMap.emptyWithCapacity.insert .PC pc }

private def emptyTrace (pc : BitVec 32) : Data mersenne31Modulus NativeReducedFamily where
  rows := []
  rom := NativeFixed.table
  initial := PCState.boundary pc (4,0)
  terminal := PCState.boundary pc (4,0)
  initialMemory := []
  terminalMemory := []

private def emptySetup : SparseDecoderSetup JumpMode := ⟨[],1⟩

private theorem public_inputs (pc : BitVec 32) :
    ImageBoundary (fixedData (emptyTrace pc)) (before pc) [] := by
  refine ⟨by simp,rfl,?_⟩
  have read : run (SailRV32.Functions.get_arch_pc ()) (before pc) = .ok pc (before pc) := by
    apply read_register
    simp [before]
  change initialState (before pc) (4,0) = some (PCState.boundary pc (4,0))
  simp only [initialState,read]

private theorem accepted (pc : BitVec 32) : Accepted (fixedData (emptyTrace pc)) := by
  constructor
  · intro row present; simp [fixedData,emptyTrace] at present
  · intro row present; simp [fixedData,emptyTrace] at present
  · exact List.Perm.refl _
  · exact List.Perm.refl _

private theorem decoded (pc : BitVec 32) :
    JumpDecodedTrace (fixedData (emptyTrace pc)) emptySetup := by
  intro row present; simp [fixedData,emptyTrace] at present

/-- A concrete actual-native zero-row trace passes the complete public execution
    boundary for every RV32 PC, with no assumed terminal bound or Sail states. -/
theorem empty_execution (pc : BitVec 32) :
    (emptyTrace pc).terminal.word.Bounded ∧
    Realizes (StepWith jumpDecoderFields registerClause emptySetup.program)
      (fixedData (emptyTrace pc)) (before pc) [] := by
  exact public_jump_execution (count := 0) (logCapacity := 0) rfl
    (public_inputs pc) (accepted pc) (decoded pc) (by
      constructor
      · intro nonempty
        exact False.elim (nonempty rfl)
      · rintro ⟨entry,member,args,_⟩
        cases member) (by simp)

/-- The actual terminal PC reader is recovered even at the top RV32 word; an
    empty path does not fabricate PC+4 or require an instruction alignment input. -/
theorem empty_top_endpoint : ∃ after : State,
    Relation.ReflTransGen (StepWith jumpDecoderFields registerClause emptySetup.program)
      (before 0xffffffff) after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok (0xffffffff : BitVec 32) after := by
  obtain ⟨after,steps,pc,_⟩ := (empty_execution 0xffffffff).2
  have canonical : (emptyTrace 0xffffffff).terminal.word.toBitVec = 0xffffffff := by decide +kernel
  change run (SailRV32.Functions.get_arch_pc ()) after =
    .ok (emptyTrace 0xffffffff).terminal.word.toBitVec after at pc
  rw [canonical] at pc
  exact ⟨after,steps,pc⟩

end Tests.NativeReducedJumpFetched
