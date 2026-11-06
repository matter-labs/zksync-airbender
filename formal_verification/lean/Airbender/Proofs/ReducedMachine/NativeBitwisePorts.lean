import Airbender.Proofs.ReducedMachine.NativeBitwiseFields
import Airbender.Proofs.ReducedMachine.NativeShiftPorts
import Airbender.Proofs.ReducedMachine.NativeBitwiseDecoder
import Airbender.Proofs.Trace.PortReads

namespace Airbender.ReducedMachine.NativeBitwisePortProofs
open Native Arithmetic Verification Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Exact regenerated metadata: both source accesses refresh only their clocks. -/
theorem readonly_sources : importedConstraintsMemoryPorts[0].writeValue = none ∧
    importedConstraintsMemoryPorts[1].writeValue = none := NativeShiftPortProofs.readonly_sources

theorem source_addresses : importedConstraintsMemoryPorts[0].address = MemoryAddress.register 5 ∧
    importedConstraintsMemoryPorts[1].address = MemoryAddress.mixed 88 true #v[39,40] := NativeShiftPortProofs.source_addresses

/-- Actual bitwise flags route the second port to readonly original rs2. -/
theorem source_two_fields {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mode : BitwiseMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) :
    w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1 :=
  NativeBitwiseFieldProofs.source_port holds mode.useRegister mask

/-- Original public decoder fields identify all actual native register cells.
    Both mixed addresses are proved register addresses using native equations. -/
theorem register_addresses {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : BitwiseProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : bitwiseDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    ∀ i : Fin 3, importedConstraintsMemoryPorts[i].address.code w =
      (Cell.register (#v[entry.data.rs1,entry.data.rs2,entry.data.rd])[i]).addressCode := by
  have decoded := NativeBitwiseDecoderProofs.decoded_fields fields query
  have mask := decoded.mask
  have second := source_two_fields holds entry.data.family mask
  have rs1 : (w 5).val = entry.data.rs1.toNat := by
    rw [decoded.rs1,ZMod.val_natCast_of_lt (lt_trans entry.data.rs1.isLt (by decide))]
  have rs2 : (w 6).val = entry.data.rs2.toNat := by
    rw [decoded.rs2,ZMod.val_natCast_of_lt (lt_trans entry.data.rs2.isLt (by decide))]
  have rd : (rdIndex w).val = entry.data.rd.toNat := by
    rw [decoded.rd,ZMod.val_natCast_of_lt (lt_trans entry.data.rd.isLt (by decide))]
  intro i
  fin_cases i
  · simp [importedConstraintsMemoryPorts,MemoryAddress.code,Cell.addressCode,rs1]
  · simp [importedConstraintsMemoryPorts,MemoryAddress.code,pairCode,Cell.addressCode,
      second.1,second.2.1,second.2.2,rs2]
  · change rdPort.address.code w = (Cell.register entry.data.rd).addressCode
    rw [(NativeBitwiseFieldProofs.write holds entry.data.family.useRegister mask).1,rd]
    rfl

abbrev nativeEvents (epoch : Nat) (w : Nat → ZMod mersenne31Modulus) :=
  Trace.nativeRowEvents epoch importedConstraintsTraceColumns importedConstraintsMemoryPorts w

/-- Readonly refreshes preserve one actual Sail pre-state for all reads, including aliases. -/
theorem register_reads {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : BitwiseProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : bitwiseDecoderFields entry.instruction = some entry.data)
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
    {w : Nat → ZMod mersenne31Modulus} {entry : BitwiseProgramEntry} {cells : List Cell} (epoch : Nat)
    {before after : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : bitwiseDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (nativeEvents epoch w).reverse before after) :
    run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (memoryWord (importedConstraintsMemoryPorts[2].writeCode w))) before = .ok () after :=
  Trace.Proofs.native_history_write epoch rfl readonly_sources.1 readonly_sources.2 history (by rfl)
    (register_addresses holds fields query 2)

end Airbender.ReducedMachine.NativeBitwisePortProofs
