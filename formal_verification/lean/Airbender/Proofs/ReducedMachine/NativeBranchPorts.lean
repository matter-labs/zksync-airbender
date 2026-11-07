import Airbender.Proofs.ReducedMachine.NativeBranchFields
import Airbender.Proofs.ReducedMachine.NativeShiftPorts
import Airbender.Proofs.ReducedMachine.NativeBranchDecoder
import Airbender.Proofs.Trace.PortReads

namespace Airbender.ReducedMachine.NativeBranchPortProofs
open Native Arithmetic Verification Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Exact regenerated metadata: both source accesses refresh only their clocks. -/
theorem readonly_sources : importedConstraintsMemoryPorts[0].writeValue = none ∧
    importedConstraintsMemoryPorts[1].writeValue = none := NativeShiftPortProofs.readonly_sources

theorem source_addresses : importedConstraintsMemoryPorts[0].address = MemoryAddress.register 5 ∧
    importedConstraintsMemoryPorts[1].address = MemoryAddress.mixed 88 true #v[39,40] := NativeShiftPortProofs.source_addresses

/-- Actual branch flags route the second port to readonly original rs2. -/
theorem source_two_fields {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) :
    w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1 :=
  NativeBranchFieldProofs.source_port holds mask

/-- Original public decoder fields identify all actual native register cells.
    Both mixed addresses are proved register addresses using native equations. -/
theorem register_addresses {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : BranchProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : branchDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    ∀ i : Fin 3, importedConstraintsMemoryPorts[i].address.code w =
      (Cell.register (#v[entry.data.rs1,entry.data.rs2,entry.data.rd])[i]).addressCode := by
  have decoded := NativeBranchDecoderProofs.decoded_fields fields query
  have mask := decoded.mask
  have second := source_two_fields holds mask
  have rs1 : (w 5).val = entry.data.rs1.toNat := by
    rw [decoded.rs1,ZMod.val_natCast_of_lt (lt_trans entry.data.rs1.isLt (by decide))]
  have rs2 : (w 6).val = entry.data.rs2.toNat := by
    rw [decoded.rs2,ZMod.val_natCast_of_lt (lt_trans entry.data.rs2.isLt (by decide))]
  have rd : entry.data.rd = 0 := (NativeBranchDecoderProofs.field_bounds fields).2.2.1
  intro i
  fin_cases i
  · simp [importedConstraintsMemoryPorts,MemoryAddress.code,Cell.addressCode,rs1]
  · simp [importedConstraintsMemoryPorts,MemoryAddress.code,pairCode,Cell.addressCode,
      second.1,second.2.1,second.2.2,rs2]
  · change rdPort.address.code w = (Cell.register entry.data.rd).addressCode
    rw [(NativeBranchFieldProofs.dummy_port holds mask).1,rd]
    rfl

abbrev nativeEvents (epoch : Nat) (w : Nat → ZMod mersenne31Modulus) :=
  Trace.nativeRowEvents epoch importedConstraintsTraceColumns importedConstraintsMemoryPorts w

/-- Readonly refreshes preserve one actual Sail pre-state for all reads, including aliases. -/
theorem register_reads {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : BranchProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : branchDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (nativeEvents epoch w).reverse before after) :
    ∀ i : Fin 3, run (SailRV32.Functions.rX_bits
      (.Regidx (#v[entry.data.rs1,entry.data.rs2,entry.data.rd])[i])) before =
        .ok (memoryWord (importedConstraintsMemoryPorts[i].readCode w)) before := by
  intro i
  have present : importedConstraintsMemoryPorts[i] ∈ importedConstraintsMemoryPorts := by
    fin_cases i <;> simp [importedConstraintsMemoryPorts]
  exact Trace.Proofs.native_history_read epoch rfl readonly_sources.1 readonly_sources.2 history present
    (register_addresses holds fields query i)

/-- The actual masked third-port word is the original Sail destination write. -/
theorem register_write {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : BranchProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : branchDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (nativeEvents epoch w).reverse before after) :
    run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (memoryWord (importedConstraintsMemoryPorts[2].writeCode w))) before = .ok () after :=
  Trace.Proofs.native_history_write epoch rfl readonly_sources.1 readonly_sources.2 history (by rfl)
    (register_addresses holds fields query 2)

/-- The present zero-write x0 port is an actual whole-data-state stutter.
    Its old read and both readonly refreshes remain in native history. -/
theorem register_stutter {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : BranchProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : branchDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (nativeEvents epoch w).reverse before after) : after = before := by
  have write := register_write epoch holds fields query history
  rw [(NativeBranchDecoderProofs.field_bounds fields).2.2.1] at write
  change EStateM.Result.ok () before = EStateM.Result.ok () after at write
  exact (EStateM.Result.ok.inj write).2.symm

end Airbender.ReducedMachine.NativeBranchPortProofs
