import Airbender.Review.Trace.Families.ReducedMachine.BranchRegisters
import Tests.NativeReducedRegisters

namespace Tests.NativeReducedBranchRegisters
open Airbender Arithmetic Trace ReducedMachine Native Verification
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The selected native branch mask reject a mixed source address that differs from rs2. -/
theorem wrong_source_index_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) (bad : w 39 ≠ w 6) : False :=
  bad (NativeBranchPortProofs.source_two_fields native mask).1

theorem high_source_address_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) (bad : w 40 ≠ 0) : False :=
  bad (NativeBranchPortProofs.source_two_fields native mask).2.1

theorem ram_source_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) (bad : w 88 ≠ 1) : False :=
  bad (NativeBranchPortProofs.source_two_fields native mask).2.2

/-- Aliases obtain equal source words from one actual Sail pre-state. -/
theorem aliased_source_reads {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : BranchProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : branchDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (NativeBranchPortProofs.nativeEvents epoch w).reverse before after)
    (sameIndex : entry.data.rs1 = entry.data.rs2) :
    memoryWord (importedConstraintsMemoryPorts[0].readCode w) =
      memoryWord (importedConstraintsMemoryPorts[1].readCode w) := by
  have left := NativeBranchPortProofs.register_reads epoch native fields query history 0
  have right := NativeBranchPortProofs.register_reads epoch native fields query history 1
  change run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before = _ at left
  change run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before = _ at right
  rw [sameIndex] at left
  exact (EStateM.Result.ok.inj (left.symm.trans right)).1

/-- The present dummy old read is x0, including source/dummy aliases. -/
theorem dummy_read_zero {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : BranchProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : branchDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (NativeBranchPortProofs.nativeEvents epoch w).reverse before after) :
    memoryWord (importedConstraintsMemoryPorts[2].readCode w) = 0 := by
  have read := NativeBranchPortProofs.register_reads epoch native fields query history 2
  change run (SailRV32.Functions.rX_bits (.Regidx entry.data.rd)) before = _ at read
  rw [(NativeBranchDecoderProofs.field_bounds fields).2.2.1] at read
  change EStateM.Result.ok (0 : BitVec 32) before = _ at read
  exact (EStateM.Result.ok.inj read).1.symm

/-- Both readonly refreshes and the present dummy write stutter all data. -/
theorem dummy_state {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : BranchProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : branchDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (NativeBranchPortProofs.nativeEvents epoch w).reverse before after) :
    after = before := NativeBranchPortProofs.register_stutter epoch native fields query history

/-- Initialized native matching and proved masking reject nonzero actual x0 events. -/
theorem initialized_nonzero_x0_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : branchDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : BranchDecodedTrace trace setup) {event : MemoryAccess}
    (present : event ∈ trace.nativeEvents) (address : event.2.1 = (Cell.register 0).addressCode)
    (bad : memoryWord event.2.2.2 ≠ 0) : False :=
  bad (NativeBranchRegisterProofs.native_zero_writes image accepted
    (Trace.Proofs.image_clock_boundary (by decide) inputs) inputs.image decoded event present address)

/-- Positive exact imported-port/group mechanics fixture: all three ports alias
    x0 and refresh/write zero. This assignment is not claimed to satisfy the
    complete 117-equation circuit or its instruction decoder. -/
theorem positive_x0_group (before : State) :
    SailHistory [Cell.register 0]
      (NativeBranchPortProofs.nativeEvents 0 (fun i => if i = 88 ∨ i = 89 then 1 else 0)).reverse
      before before :=
  Tests.NativeReducedRegisters.positive_x0_group before

end Tests.NativeReducedBranchRegisters
