import Airbender.Review.Trace.Families.ReducedMachine.Registers

namespace Tests.NativeReducedRegisters
open Airbender Arithmetic Trace ReducedMachine Native Verification
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- All six selected masks reject a mixed source address that differs from rs2. -/
theorem wrong_source_index_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) (bad : w 39 ≠ w 6) : False :=
  bad (NativeShiftPortProofs.source_two_fields native mode useRegister mask).1

theorem high_source_address_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) (bad : w 40 ≠ 0) : False :=
  bad (NativeShiftPortProofs.source_two_fields native mode useRegister mask).2.1

theorem ram_source_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus)) (bad : w 88 ≠ 1) : False :=
  bad (NativeShiftPortProofs.source_two_fields native mode useRegister mask).2.2

/-- Aliases obtain equal source words from one actual Sail pre-state. -/
theorem aliased_source_reads {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (NativeShiftPortProofs.nativeEvents epoch w).reverse before after)
    (sameIndex : entry.data.rs1 = entry.data.rs2) :
    memoryWord (importedConstraintsMemoryPorts[0].readCode w) =
      memoryWord (importedConstraintsMemoryPorts[1].readCode w) := by
  have left := NativeShiftPortProofs.register_reads epoch native fields query history 0
  have right := NativeShiftPortProofs.register_reads epoch native fields query history 1
  change run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before = _ at left
  change run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before = _ at right
  rw [sameIndex] at left
  exact (EStateM.Result.ok.inj (left.symm.trans right)).1

/-- An old-destination alias reads that same pre-state, before the real write. -/
theorem aliased_destination_read {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (NativeShiftPortProofs.nativeEvents epoch w).reverse before after)
    (sameIndex : entry.data.rs1 = entry.data.rd) :
    memoryWord (importedConstraintsMemoryPorts[0].readCode w) =
      memoryWord (importedConstraintsMemoryPorts[2].readCode w) := by
  have left := NativeShiftPortProofs.register_reads epoch native fields query history 0
  have destination := NativeShiftPortProofs.register_reads epoch native fields query history 2
  change run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before = _ at left
  change run (SailRV32.Functions.rX_bits (.Regidx entry.data.rd)) before = _ at destination
  rw [sameIndex] at left
  exact (EStateM.Result.ok.inj (left.symm.trans destination)).1

/-- Discarding x0 preserves the whole original Sail data state, with all reads retained. -/
theorem discarded_state {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (NativeShiftPortProofs.nativeEvents epoch w).reverse before after)
    (discarded : entry.data.rd = 0) : after = before := by
  have write := NativeShiftPortProofs.register_write epoch native fields query history
  rw [discarded] at write
  change EStateM.Result.ok () before = EStateM.Result.ok () after at write
  exact (EStateM.Result.ok.inj write).2.symm

/-- Initialized native matching and proved masking reject nonzero actual x0 events. -/
theorem initialized_nonzero_x0_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : shiftDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup) {event : MemoryAccess}
    (present : event ∈ (fixedData trace).nativeEvents) (address : event.2.1 = (Cell.register 0).addressCode)
    (bad : memoryWord event.2.2.2 ≠ 0) : False :=
  bad (NativeShiftRegisterProofs.native_zero_writes image accepted
    (Trace.Proofs.image_clock_boundary (by decide) inputs) inputs.image decoded event present address)

private theorem zero_refresh {events : List MemoryAccess} {before : State}
    (past : SailHistory [Cell.register 0] events before before) (time : Nat) :
    SailHistory [Cell.register 0] ((time,0,0,0) :: events) before before :=
  .cons past (Cell.register 0) (by simp) rfl rfl rfl

/-- Positive exact imported-port/group mechanics fixture: all three ports alias
    x0 and refresh/write zero. This assignment is not claimed to satisfy the
    complete 117-equation circuit or its instruction decoder. -/
theorem positive_x0_group (before : State) :
    SailHistory [Cell.register 0]
      (NativeShiftPortProofs.nativeEvents 0 (fun i => if i = 88 ∨ i = 89 then 1 else 0)).reverse
      before before := by
  change SailHistory [Cell.register 0] [(2,0,0,0),(1,0,0,0),(0,0,0,0)] before before
  exact zero_refresh (zero_refresh (zero_refresh (.nil before) 0) 1) 2

end Tests.NativeReducedRegisters
