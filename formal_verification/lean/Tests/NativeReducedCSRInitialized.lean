import Airbender.Review.Trace.Families.ReducedMachine.CSRRegisters
import Airbender.Review.Trace.Families.ReducedMachine.CSRValues

namespace Tests.NativeReducedCSRInitialized
open Airbender Arithmetic Trace ReducedMachine Native Verification
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The selected native CSR mask reject a mixed source address that differs from rs2. -/
theorem wrong_source_index_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) (bad : w 39 ≠ w 6) : False :=
  bad (NativeCSRPortProofs.source_two_fields native mask).1

theorem high_source_address_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) (bad : w 40 ≠ 0) : False :=
  bad (NativeCSRPortProofs.source_two_fields native mask).2.1

theorem ram_source_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) (bad : w 88 ≠ 1) : False :=
  bad (NativeCSRPortProofs.source_two_fields native mask).2.2

/-- Aliases obtain equal source words from one actual Sail pre-state. -/
theorem aliased_source_reads {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : CSRProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : csrDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (NativeCSRPortProofs.nativeEvents epoch w).reverse before after)
    (sameIndex : entry.data.rs1 = entry.data.rs2) :
    memoryWord (importedConstraintsMemoryPorts[0].readCode w) =
      memoryWord (importedConstraintsMemoryPorts[1].readCode w) := by
  have left := NativeCSRPortProofs.register_reads epoch native fields query history 0
  have right := NativeCSRPortProofs.register_reads epoch native fields query history 1
  change run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before = _ at left
  change run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before = _ at right
  rw [sameIndex] at left
  exact (EStateM.Result.ok.inj (left.symm.trans right)).1

/-- An old-destination alias reads that same pre-state, before the real write. -/
theorem aliased_destination_read {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : CSRProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : csrDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (NativeCSRPortProofs.nativeEvents epoch w).reverse before after)
    (sameIndex : entry.data.rs1 = entry.data.rd) :
    memoryWord (importedConstraintsMemoryPorts[0].readCode w) =
      memoryWord (importedConstraintsMemoryPorts[2].readCode w) := by
  have left := NativeCSRPortProofs.register_reads epoch native fields query history 0
  have destination := NativeCSRPortProofs.register_reads epoch native fields query history 2
  change run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before = _ at left
  change run (SailRV32.Functions.rX_bits (.Regidx entry.data.rd)) before = _ at destination
  rw [sameIndex] at left
  exact (EStateM.Result.ok.inj (left.symm.trans destination)).1

/-- Discarding the native GPR destination preserves this GPR-transfer state, with all reads retained. -/
theorem discarded_state {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : CSRProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : csrDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (NativeCSRPortProofs.nativeEvents epoch w).reverse before after)
    (discarded : entry.data.rd = 0) : after = before := by
  have write := NativeCSRPortProofs.register_write epoch native fields query history
  rw [discarded] at write
  change EStateM.Result.ok () before = EStateM.Result.ok () after at write
  exact (EStateM.Result.ok.inj write).2.symm

/-- Initialized native matching and proved masking reject nonzero actual x0 events. -/
theorem initialized_nonzero_x0_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : csrDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : CSRDecodedTrace trace setup) {event : MemoryAccess}
    (present : event ∈ trace.nativeEvents) (address : event.2.1 = (Cell.register 0).addressCode)
    (bad : memoryWord event.2.2.2 ≠ 0) : False :=
  bad (NativeCSRRegisterProofs.native_zero_writes image accepted
    (Trace.Proofs.image_clock_boundary (by decide) inputs) inputs.image decoded event present address)

section InitializedRanges
variable {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : csrDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (runtimeCSRData trace) initial cells) (accepted : Accepted (runtimeCSRData trace))
    (decoded : CSRDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows)
include image inputs accepted decoded present

/-- Every actual port read, including source-low35 and the x0 second/OLDREAD,
    is bounded by initialized native matching rather than a supplied range. -/
theorem all_native_reads_bounded (i : Fin 3) :
    (readToken row.assignment importedConstraintsMemoryPorts[i]).word.Bounded := by
  have ranges := (public_runtime_csr_value_bounds image inputs accepted decoded).1 row present
  cases row with
  | mk family w =>
    cases family
    apply ranges
    change importedConstraintsMemoryPorts[i] ∈ importedConstraintsMemoryPorts
    fin_cases i <;> simp [importedConstraintsMemoryPorts]

theorem oversized_source_rejected (bad : 65536 ≤ (sourceWord row.assignment).lo) : False := by
  have bounds := all_native_reads_bounded image inputs accepted decoded row present 0
  rw [Trace.Proofs.read_word] at bounds
  change (sourceWord row.assignment).Bounded at bounds
  have low := bounds.1
  change _ < 65536 at low
  omega

theorem oversized_second_read_rejected (bad : 65536 ≤ (row.assignment 37).val) : False := by
  have bounds := all_native_reads_bounded image inputs accepted decoded row present 1
  rw [Trace.Proofs.read_word] at bounds
  change (row.assignment 37).val < 65536 ∧ (row.assignment 38).val < 65536 at bounds
  omega

theorem oversized_written_rejected (bad : 65536 ≤ (rdWrite row.assignment)[0].val) : False := by
  have ranges := (public_runtime_csr_value_bounds image inputs accepted decoded).2.1 row present
  cases row with
  | mk family w =>
    cases family
    have bounds := ranges importedConstraintsMemoryPorts[2] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.write_word] at bounds
    change (rdWrite w)[0].val < 65536 ∧ (rdWrite w)[1].val < 65536 at bounds
    change 65536 ≤ (rdWrite w)[0].val at bad
    exact (Nat.not_le_of_gt bounds.1) bad

/-- The actual second readonly refresh is original x0, not a discarded read. -/
theorem readonly_x0_read_zero :
    (row.assignment 37).val = 0 ∧ (row.assignment 38).val = 0 := by
  have holds := accepted.constraints row present
  obtain ⟨entry,found,source,query,_⟩ := NativeCSRDecoderProofs.trace_decoding image accepted decoded row present
  have zeroReads := Trace.Proofs.zero_reads_of_preserving (by decide) accepted
    (Trace.Proofs.image_clock_boundary (by decide) inputs) inputs.image
    (NativeCSRRegisterProofs.decoded_zero_preserving image accepted decoded)
  cases row with
  | mk family w =>
    cases family
    have address := NativeCSRPortProofs.register_addresses holds source.fields query 1
    change importedConstraintsMemoryPorts[1].address.code w = (Cell.register entry.data.rs2).addressCode at address
    rw [(NativeCSRDecoderProofs.field_bounds source.fields).2.2.1] at address
    have zero := zeroReads _ present importedConstraintsMemoryPorts[1]
      (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) address
    change Nat.pair (w 37).val (w 38).val = Nat.pair 0 0 at zero
    exact Nat.pair_eq_pair.mp zero
end InitializedRanges

/-- The actual terminal token range is propagated from public seeds and writes. -/
theorem oversized_terminal_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : csrDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (runtimeCSRData trace) initial cells) (accepted : Accepted (runtimeCSRData trace))
    (decoded : CSRDecodedTrace trace setup) {token : MemoryToken mersenne31Modulus}
    (present : token ∈ trace.terminalMemory) (bad : 65536 ≤ token.word.lo) : False := by
  have bounds := (public_runtime_csr_value_bounds image inputs accepted decoded).2.2 token present
  have low := bounds.1
  change _ < 65536 at low
  omega

private def groupAssignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 9 then 1984 else if i = 12 then 129 else
    if i = 8 ∨ i = 11 ∨ i = 17 ∨ i = 24 ∨ i = 88 ∨ i = 89 then 1 else 0
private def groupEntry : CSRProgramEntry :=
  ⟨0,0x7c001073,.CSRReg (1984,.Regidx 0,.Regidx 0,.CSRRW),⟨(),0,0,0,⟨1984,0⟩,129,1⟩⟩

theorem partial_group_decoding : csrDecoderFields groupEntry.instruction = some groupEntry.data ∧
    decoderQuery groupAssignment = groupEntry.query := by constructor; rfl; decide +kernel

private theorem zero_refresh {before : State} {events : List MemoryAccess}
    (past : SailHistory [Cell.register 0] events before before) (time : Nat) :
    SailHistory [Cell.register 0] ((time,0,0,0) :: events) before before :=
  .cons past (Cell.register 0) (by simp) rfl rfl rfl

/-- Positive actual three-port CSR GPR group with raw x0 fields. These mechanics
    do not assert all117 equations/22 lookups, initialized acceptance or CSR execution. -/
theorem positive_csr_x0_group (before : State) :
    SailHistory [Cell.register 0] (NativeCSRPortProofs.nativeEvents 0 groupAssignment).reverse before before := by
  change SailHistory [Cell.register 0] [(2,0,0,0),(1,0,0,0),(0,0,0,0)] before before
  exact zero_refresh (zero_refresh (zero_refresh (.nil before) 0) 1) 2
end Tests.NativeReducedCSRInitialized
