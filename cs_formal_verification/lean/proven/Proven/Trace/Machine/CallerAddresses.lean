module
public import Proven.Trace.Machine.Selectors
public import Proven.Trace.Machine.DelegateData
public import Proven.Trace.Machine.CPUEvents
public import Proven.Trace.Machine.MemoryVirtual

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Unrolled caller refreshes address x0 because the public delegation metadata has zero rs1 and rd. -/
theorem unrolled_caller_addresses {config : RVMachineConfig} {kind : RV.DelegationKind}
    {w : Nat → ZMod babyBearModulus} {entry : RVMachineProgramEntry}
    (fields : rvMachineDecoderFields config (.delegate kind) = some entry.data)
    (query : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (selected : w 17 = 1) :
    ∀ event ∈ cpuEvents (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily)
      (Caller.machinePorts ⟨.addSub, w⟩), event.2.1 = (Cell.register 0).addressCode := by
  have data := (machine_delegate_fields fields).2
  have rs := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[2]) query
  have dest := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[4]) query
  rw [data] at rs dest
  have rsZero : w 5 = 0 := by
    simpa [Row.decoderQuery, nativeDecoderQuery, Row.columns, Row.decoderColumns,
      CircuitLayout.columns, CircuitLayout.decoderColumns, AddSub.importedConstraintsTraceColumns,
      AddSub.importedConstraintsDecoderColumns, RVMachineDecoderData.row] using rs
  have rdZero : w 7 = 0 := by
    simpa [Row.decoderQuery, nativeDecoderQuery, Row.columns, Row.decoderColumns,
      CircuitLayout.columns, CircuitLayout.decoderColumns, AddSub.importedConstraintsTraceColumns,
      AddSub.importedConstraintsDecoderColumns, RVMachineDecoderData.row] using dest
  have live : ((⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).family == .addSub &&
      decide (Requests.Selected w)) = true := by
    simpa [Requests.Selected, AddSub.importedConstraintsDecoderColumns] using selected
  have ports : Caller.machinePorts (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) = Caller.architecturalPorts := by
    unfold Caller.machinePorts
    exact ite_eq_left live
  intro event present
  obtain ⟨port, included, rfl⟩ := List.mem_map.mp present
  rw [ports] at included
  have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨ port = AddSub.importedConstraintsMemoryPorts[2] := by
    simpa [Caller.architecturalPorts] using included
  change port.address.code w = (Cell.register 0).addressCode
  rcases modes with rfl | rfl
  · simp [AddSub.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, rsZero]
  · simp [AddSub.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, rdZero]

/-- Unified caller refreshes address x0 under the same full-CSR public metadata. -/
theorem unified_caller_addresses {kind : RV.DelegationKind}
    {setup : Table (ZMod babyBearModulus) (fields 10)} {w : Nat → ZMod babyBearModulus} {entry : RVMachineProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.importedConstraints setup))
    (fields : rvMachineDecoderFields .unified (.delegate kind) = some entry.data)
    (query : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (selected : w 18 = 1) :
    ∀ event ∈ cpuEvents (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)
      (UnifiedReduced.Caller.machinePorts ⟨.machine, w⟩), event.2.1 = (Cell.register 0).addressCode := by
  have data := (machine_delegate_fields fields).2
  have flags := unified_machine_selectors core query (by rw [data]; change (128 : Nat) < 524288; decide)
  have noStore : w 29 = 0 := by
    have flag := flags ⟨18, by decide⟩
    rw [data] at flag
    simpa [UnifiedReduced.importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
  have rs := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[2]) query
  have dest := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[4]) query
  rw [data] at rs dest
  have rsZero : w 5 = 0 := by
    simpa [Row.decoderQuery, nativeDecoderQuery, Row.columns, Row.decoderColumns,
      CircuitLayout.columns, CircuitLayout.decoderColumns, UnifiedReduced.importedConstraintsTraceColumns,
      UnifiedReduced.importedConstraintsDecoderColumns, RVMachineDecoderData.row] using rs
  have rdZero : w 7 = 0 := by
    simpa [Row.decoderQuery, nativeDecoderQuery, Row.columns, Row.decoderColumns,
      CircuitLayout.columns, CircuitLayout.decoderColumns, UnifiedReduced.importedConstraintsTraceColumns,
      UnifiedReduced.importedConstraintsDecoderColumns, RVMachineDecoderData.row] using dest
  have low := Verification.assertion_of_holds core ⟨28, by rw [UnifiedReduced.constraint_count]; decide⟩
  have high := Verification.assertion_of_holds core ⟨29, by rw [UnifiedReduced.constraint_count]; decide⟩
  op_index at low high
  simp [Expression.eval, Verification.environment, noStore] at low high
  have location : w 44 = w 7 := by linear_combination low
  have upper : w 45 = 0 := by linear_combination high
  rw [rdZero] at location
  have ports : UnifiedReduced.Caller.machinePorts (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) =
      UnifiedReduced.Caller.architecturalPorts := by
    unfold UnifiedReduced.Caller.machinePorts
    exact ite_eq_left selected
  intro event present
  obtain ⟨port, included, rfl⟩ := List.mem_map.mp present
  rw [ports] at included
  have modes : port = UnifiedReduced.importedConstraintsMemoryPorts[0] ∨
      port = UnifiedReduced.importedConstraintsMemoryPorts[2] := by
    simpa [UnifiedReduced.Caller.architecturalPorts] using included
  change port.address.code w = (Cell.register 0).addressCode
  rcases modes with rfl | rfl
  · simp [UnifiedReduced.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, rsZero]
  · simp [UnifiedReduced.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
      Cell.addressCode, noStore, location, upper]

end Airbender.Trace.Machine.Proofs
