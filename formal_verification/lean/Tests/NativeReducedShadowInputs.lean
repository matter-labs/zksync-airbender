import Airbender.Review.Trace.Families.ReducedMachine.ShadowInputs
import Airbender.Review.Trace.Families.ReducedMachine.WordMemoryShadowValues
import Airbender.Review.Trace.Families.ReducedMachine.WordMemoryShadowResults

namespace Tests.NativeReducedShadowInputs
open Airbender Arithmetic Trace ReducedMachine Native NativeShadow
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def before : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity.insert .PC (0 : BitVec 32)).insert .x1 (16 : BitVec 32)
    mem := Std.ExtHashMap.emptyWithCapacity }
private def cells : List Cell := [.register 1]
private def seeds : List ShadowSeed := [(16,123)]
private def trace : Data mersenne31Modulus NativeReducedFamily where
  rows := []
  rom := NativeFixed.table
  initial := PCState.boundary 0 (4,0)
  terminal := PCState.boundary 0 (4,0)
  initialMemory := [(Cell.register 1).initialToken (16 : BitVec 32)] ++ shadowTokens seeds
  terminalMemory := [(Cell.register 1).initialToken (16 : BitVec 32)] ++ shadowTokens seeds
private def setup : SparseDecoderSetup WordMemoryMode := ⟨[],1⟩

/-- The native shadow initializer succeeds without a Sail byte at its address. -/
theorem independent_public_inputs : ShadowImageBoundary (fixedData trace) before cells seeds := by
  constructor
  · decide +kernel
  · intro cell present
    have same : cell = .register 1 := by simpa [cells] using present
    subst cell
    exact NativeShadowProofs.architectural_register _
  · intro seed present
    have same : seed = ((16 : BitVec 32),(123 : BitVec 32)) := by simpa [seeds] using present
    subst seed
    decide +kernel
  · have read : (Cell.register (1 : BitVec 5)).read before = .ok (16 : BitVec 32) before := by
      apply read_register
      simp [before]
    simp only [shadowInitialImage,initialImage,cells,List.mapM_cons,List.mapM_nil]
    rw [read]
    rfl
  · have read : run (SailRV32.Functions.get_arch_pc ()) before = .ok (0 : BitVec 32) before := by
      apply read_register
      simp [before,Std.ExtDHashMap.get?_insert]
    change initialState before (4,0) = some (PCState.boundary 0 (4,0))
    simp only [initialState,read]

theorem missing_shadow_byte : (Cell.ram (16 : BitVec 32)).read before =
    .error (_root_.Sail.Error.OutOfMemoryRange 16) before := by
  simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
    EStateM.run,get,getThe,MonadStateOf.get,bind,EStateM.bind,EStateM.get,throw,throwThe,MonadExceptOf.throw,EStateM.throw,before]

/-- The native ledger value123 is independent of the actual fixed ROM value at16. -/
theorem independent_shadow_value :
    ((shadowTokens (p := mersenne31Modulus) seeds)[0]'(by decide)).word.toBitVec = 123 ∧
    wordMemoryROMWord 4 = ⟨21015,0⟩ := by decide +kernel

theorem public_projection : initialImage (p := mersenne31Modulus) before cells =
    some ((fixedData trace).initialMemory.filter fun token => architecturalAddress token.address) :=
  (public_shadow_initialization independent_public_inputs).1

theorem public_seed_ranges : ∀ token ∈ (fixedData trace).initialMemory, token.word.Bounded :=
  (public_shadow_initialization independent_public_inputs).2.2.2

private theorem accepted : Accepted (fixedData trace) := by
  constructor
  · intro row present; simp [fixedData,trace] at present
  · intro row present; simp [fixedData,trace] at present
  · exact List.Perm.refl _
  · exact List.Perm.refl _

private theorem decoded : WordMemoryDecodedTrace (fixedData trace) setup := by
  intro row present; simp [fixedData,trace] at present

/-- Complete public independent-shadow input/range scope on an actual native
    empty trace. This is not a complete accepted LW/SW row or Sail execution. -/
theorem initialized_shadow_ranges :
    (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ (fixedData trace).terminalMemory, token.word.Bounded) :=
  public_word_memory_shadow_value_bounds (count := 0) (logCapacity := 0) rfl
    independent_public_inputs accepted decoded

theorem duplicate_shadow_rejected :
    ¬ ShadowImageBoundary (fixedData trace) before cells [(16,123),(16,456)] := by
  intro inputs
  have impossible := inputs.domain
  simp [cells] at impossible

theorem nonshadow_seed_rejected :
    ¬ ShadowImageBoundary (fixedData trace) before cells [(4194304,123)] := by
  intro inputs
  have impossible := inputs.shadows ((4194304 : BitVec 32),(123 : BitVec 32)) (by simp)
  have literal : (4194304 : BitVec 32).toNat = 4194304 := rfl
  rw [literal] at impossible
  omega

end Tests.NativeReducedShadowInputs
