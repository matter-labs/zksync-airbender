import Airbender.Review.Trace.Families.ReducedMachine.WordMemoryFetchedExecution

namespace Tests.NativeReducedWordMemoryFetched
open Airbender ReducedMachine Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def base (pc : BitVec 32) : State :=
  { (default : State) with
    regs := Std.ExtDHashMap.emptyWithCapacity.insert .PC pc
    mem := Std.ExtHashMap.emptyWithCapacity }
private def initial (pc : BitVec 32) : State := NativeROM.state (base pc)
private def cells : List Cell := [.register 0]
private def seeds : List ShadowSeed := [(16,123)]
private def trace (pc : BitVec 32) : Data mersenne31Modulus NativeReducedFamily where
  rows := []
  rom := NativeFixed.table
  initial := PCState.boundary pc (4,0)
  terminal := PCState.boundary pc (4,0)
  initialMemory := [(Cell.register 0).initialToken 0]++shadowTokens seeds
  terminalMemory := [(Cell.register 0).initialToken 0]++shadowTokens seeds
private def setup : SparseDecoderSetup WordMemoryMode := ⟨[],1⟩
private theorem inputs (pc : BitVec 32) : ShadowImageBoundary (fixedData (trace pc)) (initial pc) cells seeds := by
  constructor
  · decide
  · intro cell member
    have same : cell = .register 0 := by simpa [cells] using member
    subst cell
    exact NativeShadowProofs.architectural_register 0
  · intro seed member
    have same : seed = ((16 : BitVec 32),(123 : BitVec 32)) := by simpa [seeds] using member
    subst seed
    decide
  · have zero : (Cell.register 0).read (initial pc) = .ok (0 : BitVec 32) (initial pc) := by rfl
    simp only [shadowInitialImage,initialImage,cells,List.mapM_cons,List.mapM_nil,zero]
    rfl
  · have read : run (SailRV32.Functions.get_arch_pc ()) (initial pc) = .ok pc (initial pc) := by
      apply read_register
      change (NativeROM.state (base pc)).regs.get? .PC = some pc
      rw [NativeROMProofs.registers]
      simp [base]
    change initialState (initial pc) (4,0) = some (PCState.boundary pc (4,0))
    simp only [initialState,read]
private theorem accepted (pc : BitVec 32) : Accepted (fixedData (trace pc)) := by
  constructor
  · intro row present; simp [fixedData,trace] at present
  · intro row present; simp [fixedData,trace] at present
  · exact List.Perm.refl _
  · exact List.Perm.refl _
private theorem decoded (pc : BitVec 32) : WordMemoryDecodedTrace (fixedData (trace pc)) setup := by
  intro row present; simp [fixedData,trace] at present

/-- Complete actual-native EMPTY public execution for EVERY RV32 PC, with real
    architectural x0 terminal matching, independent shadow123 and no CSR premise. -/
theorem empty_execution [MemoryPlatform SailRV32.exception] (pc : BitVec 32) :
    (trace pc).terminal.word.Bounded ∧ WordMemoryRealizes setup.program (fixedData (trace pc)) (initial pc) cells :=
  public_word_memory_execution (count := 0) (logCapacity := 0) rfl (inputs pc) (accepted pc) (decoded pc)
    (by
      intro cell member
      have same : cell = .register 0 := by simpa [cells] using member
      subst cell
      trivial)
    (by decide) (by intro nonempty; exact False.elim (nonempty rfl))
    (by intro address member; simp [cells] at member)

/-- The public conclusion derives the actual top RV32 PC reader and x0 terminal
    reader. Ignored shadow123 remains in native matching and is not an x0/ROM read. -/
theorem top_terminal_readers [MemoryPlatform SailRV32.exception] : ∃ after : State,
    Relation.ReflTransGen (StepWith wordMemoryDecoderFields wordMemoryClause setup.program) (initial 0xffffffff) after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok (0xffffffff : BitVec 32) after ∧
    (Cell.register 0).read after = .ok (0 : BitVec 32) after := by
  obtain ⟨after,steps,pc,reads⟩ := (empty_execution 0xffffffff).2
  have canonical : (trace 0xffffffff).terminal.word.toBitVec = 0xffffffff := by decide +kernel
  change run (SailRV32.Functions.get_arch_pc ()) after = .ok (trace 0xffffffff).terminal.word.toBitVec after at pc
  rw [canonical] at pc
  obtain ⟨cell,member,address,read⟩ := reads ((Cell.register 0).initialToken 0)
    (by simp [fixedData,trace]) (NativeShadowProofs.architectural_register 0)
  have same : cell = .register 0 := by simpa [cells] using member
  subst cell
  have value : ((Cell.register 0).initialToken (p := mersenne31Modulus) 0).word.toBitVec = (0 : BitVec 32) := by decide +kernel
  rw [value] at read
  exact ⟨after,steps,pc,read⟩

end Tests.NativeReducedWordMemoryFetched
