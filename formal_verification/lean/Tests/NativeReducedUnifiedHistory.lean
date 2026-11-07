import Airbender.Review.Trace.Families.ReducedMachine.UnifiedHistory
import Airbender.Review.Trace.Families.ReducedMachine.UnifiedValues

namespace Tests.NativeReducedUnifiedHistory
open Airbender ReducedMachine Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Even source x0 is a retained actual port; projection is by address space. -/
theorem source_cannot_be_filtered {w : Nat → ZMod mersenne31Modulus} {entry : UnifiedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (bad : architecturalAddress (importedConstraintsMemoryPorts[0].address.code w) = false) : False := by
  have actual := NativeUnifiedLocalProofs.port_domains holds fields query 0
  cases family : entry.data.family <;> simp [unifiedPortDomains,family,bad] at actual

theorem store_memory_cannot_be_filtered {w : Nat → ZMod mersenne31Modulus} {entry : UnifiedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (bad : architecturalAddress (importedConstraintsMemoryPorts[2].address.code w) = false) : False := by
  have actual := NativeUnifiedLocalProofs.port_domains holds fields query 2
  cases family : entry.data.family <;> simp [unifiedPortDomains,family,bad] at actual

theorem rom_shadow_must_be_filtered {w : Nat → ZMod mersenne31Modulus} {entry : UnifiedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (load : entry.data.family = .inr false) (inside : (wordMemoryAddressWord w).hi < 64)
    (bad : architecturalAddress (importedConstraintsMemoryPorts[1].address.code w) = true) : False := by
  have actual := NativeUnifiedLocalProofs.port_domains holds fields query 1
  simp [unifiedPortDomains,load,bad,Nat.not_le_of_gt inside] at actual

theorem ram_refresh_cannot_be_filtered {w : Nat → ZMod mersenne31Modulus} {entry : UnifiedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (load : entry.data.family = .inr false) (ram : 64 ≤ (wordMemoryAddressWord w).hi)
    (bad : architecturalAddress (importedConstraintsMemoryPorts[1].address.code w) = false) : False := by
  have actual := NativeUnifiedLocalProofs.port_domains holds fields query 1
  simp [unifiedPortDomains,load,bad,ram] at actual

/-- All actual native memory and register reads, including the unchecked low
    first source, must inherit canonical ranges from public initialization. -/
theorem oversized_source_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : Reference.RiscV.Sail.State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (inputs : NativeShadow.ShadowImageBoundary (fixedData trace) before cells seeds)
    (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (large : limbBase ≤ (row.assignment 35).val) : ¬ Accepted (fixedData trace) := by
  intro accepted
  have actual := (public_unified_value_bounds image inputs accepted decoded).1 row present
    importedConstraintsMemoryPorts[0] (by cases row; rename_i family w; cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at actual
  exact Nat.not_le_of_gt actual.1 large

/-- The actual second read remains bounded even when the ROM candidate ignores
    its value. It cannot be removed from native matching. -/
theorem oversized_second_read_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : Reference.RiscV.Sail.State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (inputs : NativeShadow.ShadowImageBoundary (fixedData trace) before cells seeds)
    (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (large : limbBase ≤ (row.assignment 37).val) : ¬ Accepted (fixedData trace) := by
  intro accepted
  have actual := (public_unified_value_bounds image inputs accepted decoded).1 row present
    importedConstraintsMemoryPorts[1] (by cases row; rename_i family w; cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at actual
  exact Nat.not_le_of_gt actual.1 large

theorem oversized_destination_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : Reference.RiscV.Sail.State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (inputs : NativeShadow.ShadowImageBoundary (fixedData trace) before cells seeds)
    (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (large : limbBase ≤ (row.assignment 43).val) : ¬ Accepted (fixedData trace) := by
  intro accepted
  have actual := (public_unified_value_bounds image inputs accepted decoded).2.1 row present
    importedConstraintsMemoryPorts[2] (by cases row; rename_i family w; cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  rw [Trace.Proofs.write_word] at actual
  exact Nat.not_le_of_gt actual.1 large

theorem oversized_terminal_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : Reference.RiscV.Sail.State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (inputs : NativeShadow.ShadowImageBoundary (fixedData trace) before cells seeds)
    (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (token : MemoryToken mersenne31Modulus) (present : token ∈ (fixedData trace).terminalMemory)
    (large : limbBase ≤ token.word.hi) : ¬ Accepted (fixedData trace) := by
  intro accepted
  exact Nat.not_le_of_gt ((public_unified_value_bounds image inputs accepted decoded).2.2 token present).2 large

theorem nonzero_x0_event_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    {event : MemoryAccess} (present : event ∈ (fixedData trace).nativeEvents)
    (address : event.2.1 = (Cell.register 0).addressCode) (bad : memoryWord event.2.2.2 ≠ 0) : False :=
  bad (NativeUnifiedHistoryProofs.shadow_zero_writes image inputs accepted decoded event present address)

/-- Capacity is derived for every full public instruction window. -/
theorem public_code_window {initial : State} {count logCapacity : Nat} {setup : SparseDecoderSetup UnifiedMode}
    (image : unifiedDecoderSetupImage initial count logCapacity = some setup)
    (capacity : count ≤ 1048576) {entry : UnifiedProgramEntry} (present : entry ∈ setup.program) :
    entry.pc.toNat+4 ≤ 4194304 := NativeUnifiedHistoryProofs.setup_rom_pc image capacity present

private def before : State :=
  { (default : State) with
    regs := Std.ExtDHashMap.emptyWithCapacity.insert .PC (0 : BitVec 32)
    mem := Std.ExtHashMap.emptyWithCapacity }
private def seeds : List ShadowSeed := [(16,123)]
private def trace : Data mersenne31Modulus NativeReducedFamily where
  rows := []
  rom := NativeFixed.table
  initial := PCState.boundary 0 (4,0)
  terminal := PCState.boundary 0 (4,0)
  initialMemory := [(Cell.register 0).initialToken 0]++shadowTokens seeds
  terminalMemory := [(Cell.register 0).initialToken 0]++shadowTokens seeds
private def setup : SparseDecoderSetup UnifiedMode := ⟨[],1⟩
private theorem inputs : ShadowImageBoundary (fixedData trace) before [.register 0] seeds := by
  constructor
  · decide
  · intro cell member
    have same : cell = .register 0 := by simpa using member
    subst cell
    exact NativeShadowProofs.architectural_register 0
  · intro seed member
    have same : seed = ((16 : BitVec 32),(123 : BitVec 32)) := by simpa [seeds] using member
    subst seed
    decide
  · rfl
  · have read : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before = .ok (0 : BitVec 32) before := by
      apply read_register
      simp [before]
    change initialState before (4,0) = some (PCState.boundary 0 (4,0))
    simp only [initialState,read]
private theorem accepted : Accepted (fixedData trace) := by
  constructor
  · intro row present; simp [fixedData,trace] at present
  · intro row present; simp [fixedData,trace] at present
  · exact List.Perm.refl _
  · exact List.Perm.refl _
private theorem decoded : UnifiedDecodedTrace (fixedData trace) setup := by
  intro row present; simp [fixedData,trace] at present

/-- Complete actual-native EMPTY mixed projected history retains real x0 plus
    independent shadow123, with no original byte reads or CSR premise. -/
theorem empty_public_history : UnifiedProjectedHistory (fixedData trace) setup before [.register 0] :=
  public_unified_history (count := 0) (logCapacity := 0) rfl inputs accepted decoded
    (by
      intro cell member
      have same : cell = .register 0 := by simpa using member
      subst cell
      trivial)
    (by decide)

/-- The common induction also bounds the shadow terminal token; it is not an
    architectural ROM read. These empty checks are not NONEMPTY memory acceptance. -/
theorem empty_shadow_terminal_bound :
    ((Cell.ram 16).initialToken (p := mersenne31Modulus) 123).word.Bounded := by
  have bounds := (public_unified_value_bounds (count := 0) (logCapacity := 0) rfl inputs accepted decoded).2.2
  apply bounds
  simp [fixedData,trace,shadowTokens,seeds]

end Tests.NativeReducedUnifiedHistory
