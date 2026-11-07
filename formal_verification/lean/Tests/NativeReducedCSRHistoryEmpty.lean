import Airbender.Review.Trace.Families.ReducedMachine.CSRRegisters
import Airbender.Review.Trace.Families.ReducedMachine.CSRValues

namespace Tests.NativeReducedCSRHistoryEmpty
open Airbender Arithmetic Trace ReducedMachine Native Verification Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def initial (pc : BitVec 32) : State :=
  { (default : State) with
    regs := Std.ExtDHashMap.emptyWithCapacity.insert .PC pc
    mem := Std.ExtHashMap.emptyWithCapacity }
private def cells : List Cell := [.register 0]
private def trace (pc : BitVec 32) : Data mersenne31Modulus NativeReducedFamily where
  rows := []
  rom := NativeRuntimePool.table
  initial := PCState.boundary pc (4,0)
  terminal := PCState.boundary pc (4,0)
  initialMemory := [(Cell.register 0).initialToken 0]
  terminalMemory := [(Cell.register 0).initialToken 0]
private def setup : SparseDecoderSetup CSRMode := ⟨[],1⟩
private theorem inputs (pc : BitVec 32) : ImageBoundary (runtimeCSRData (trace pc)) (initial pc) cells := by
  constructor
  · decide
  · rfl
  · have read : run (SailRV32.Functions.get_arch_pc ()) (initial pc) = .ok pc (initial pc) := by
      apply read_register
      simp [initial]
    change initialState (initial pc) (4,0) = some (PCState.boundary pc (4,0))
    simp only [initialState,read]
private theorem accepted (pc : BitVec 32) : Accepted (runtimeCSRData (trace pc)) := by
  constructor
  · intro row present; simp [runtimeCSRData,trace] at present
  · intro row present; simp [runtimeCSRData,trace] at present
  · exact List.Perm.refl _
  · exact List.Perm.refl _
private theorem decoded (pc : BitVec 32) : CSRDecodedTrace (trace pc) setup := by
  intro row present; simp [trace] at present

/-- Complete actual-native EMPTY runtime CSR GPR history retains a real x0
    terminal cell, with empty original bytes and no CSR/privilege premise. -/
theorem empty_runtime_history (pc : BitVec 32) :
    CSRRegisterHistory (runtimeCSRData (trace pc)) setup (initial pc) cells :=
  public_runtime_csr_register_history (count := 0) (logCapacity := 0) rfl
    (inputs pc) (accepted pc) (decoded pc) (by
      intro cell member
      have same : cell = .register 0 := by simpa [cells] using member
      subst cell
      trivial)

/-- The public induction bounds the actual retained terminal x0 token. -/
theorem empty_terminal_bounds (pc : BitVec 32) :
    ∀ token ∈ (trace pc).terminalMemory, token.word.Bounded :=
  (public_runtime_csr_value_bounds (count := 0) (logCapacity := 0) rfl
    (inputs pc) (accepted pc) (decoded pc)).2.2
end Tests.NativeReducedCSRHistoryEmpty
