import Airbender.Proofs.Keccak.SplitRegisterObservations
import Airbender.Proofs.Keccak.SplitNativeCallExecution
import Airbender.Proofs.Keccak.SplitCallDestinations
import Airbender.Proofs.Keccak.SplitNonzeroPorts
import Airbender.Proofs.Delegation.Atomic

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

/-- Native control and pointer reads identify all declared lane addresses.
The original aligned call layout proves that every actual port is distinct. -/
theorem native_call_addresses_distinct (cached : Bool) (row : Row babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints cached fixedSetup))
    (active : row.assignment (row.columns cached).execute = 1)
    (index : Fin 361) (before : State) (arguments : ArgumentsAt index.val before)
    (boundedReads : ∀ port ∈ row.ports cached, (readToken row.assignment port).word.Bounded)
    (registers : ∀ register : Fin 2, ∃ cell : Cell,
      cell.addressCode = (nativeRegisterPort cached row register).address.code row.assignment ∧
        cell.read before = .ok (readToken row.assignment (nativeRegisterPort cached row register)).word.toBitVec before) :
    ((row.memorySteps cached).map fun edge => edge.1.address).Nodup := by
  suffices ∃ (pointer : BitVec 32) (output : Vector Nat 7), pointer.toNat % 256 = 0 ∧
      ((row.memorySteps cached).map fun edge => (edge.1.address, edge.2.word.toBitVec)) =
        (Call.writes index pointer output).map (fun entry => (entry.1.addressCode, entry.2)) by
    obtain ⟨pointer, output, aligned, projection⟩ := this
    have addresses := congrArg (fun values : List (Nat × BitVec 32) => values.map Prod.fst) projection
    simp only [List.map_map, Function.comp_def] at addresses
    rw [addresses]
    exact Call.Proofs.writes_distinct index pointer aligned output
  cases row with
  | mk kind w =>
    cases kind with
    | columnParity =>
      have equations : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
          (if cached then ColumnParityCached.clockConstraints columnParityFixedTable else
            ColumnParity.clockConstraints columnParityFixedTable) := by cases cached <;> exact holds
      have running : w 0 = 1 := by cases cached <;> exact active
      have control := parity_call_control_binding cached w equations running index before arguments (registers 0)
      obtain ⟨pointer, _, _, aligned, pointerWord⟩ := parity_call_pointer_binding cached w index before arguments
        (boundedReads _ (native_register_port_mem cached ⟨.columnParity, w⟩ 1)) (registers 1)
      exact ⟨pointer, Call.result index (parityReferenceLanes cached false w), aligned,
        parity_call_write_projection cached w equations index control.1 control.2.2.2.2 pointer
          aligned pointerWord control.2.2.1 control.2.2.2.1⟩
    | thetaRho =>
      have equations : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
          (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable else
            ThetaRho.clockConstraints thetaRhoFixedTable) := by cases cached <;> exact holds
      have running : w 0 = 1 := by cases cached <;> exact active
      have control := theta_call_control_binding cached w equations running index before arguments (registers 0)
      obtain ⟨pointer, _, _, aligned, pointerWord⟩ := theta_call_pointer_binding cached w index before arguments
        (boundedReads _ (native_register_port_mem cached ⟨.thetaRho, w⟩ 1)) (registers 1)
      exact ⟨pointer, Call.result index (thetaReferenceLanes cached false w), aligned,
        theta_call_write_projection cached w equations index control.1 control.2.2.2.2
          (fun lane high => boundedReads _ ((theta_call_ports_present cached w).2.2 lane high))
          pointer aligned pointerWord control.2.2.1 control.2.2.2.1⟩
    | chi5 =>
      have equations : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
          (if cached then Chi5Cached.clockConstraints chi5FixedTable else
            Chi5.clockConstraints chi5FixedTable) := by cases cached <;> exact holds
      have running : w 0 = 1 := by cases cached <;> exact active
      have control := chi5_call_control_binding cached w equations running index before arguments (registers 0)
      obtain ⟨pointer, _, _, aligned, pointerWord⟩ := chi5_call_pointer_binding cached w index before arguments
        (boundedReads _ (native_register_port_mem cached ⟨.chi5, w⟩ 1)) (registers 1)
      exact ⟨pointer, Call.result index (chi5ReferenceLanes cached false w), aligned,
        chi5_call_write_projection cached w equations index control.1 pointer aligned pointerWord
          control.2.2.1 control.2.2.2⟩

/-- Initialized native history determines every actual input read. Control
and pointer observations come first; their derived layout excludes lane aliases. -/
theorem native_call_input_observations (cached : Bool) (row : Row babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints cached fixedSetup))
    (active : row.assignment (row.columns cached).execute = 1)
    (index : Fin 361) {before after : State} (arguments : ArgumentsAt index.val before)
    (boundedReads : ∀ port ∈ row.ports cached, (readToken row.assignment port).word.Bounded)
    {cells : List Cell} {events : List MemoryAccess}
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((row.memorySteps cached).map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (initial : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before) :
    ∀ port ∈ row.ports cached, ∃ cell : Cell,
      cell.addressCode = port.address.code row.assignment ∧
        cell.read before = .ok (readToken row.assignment port).word.toBitVec before := by
  have registers : ∀ register : Fin 2, ∃ cell : Cell,
      cell.addressCode = (nativeRegisterPort cached row register).address.code row.assignment ∧
        cell.read before = .ok (readToken row.assignment (nativeRegisterPort cached row register)).word.toBitVec before := by
    intro register
    obtain ⟨cell, _, address, read⟩ := native_register_observation cached row register
      history permutation aligned initial
    exact ⟨cell, address, read⟩
  have distinct := native_call_addresses_distinct cached row holds active index before arguments boundedReads registers
  have actualDistinct : (events.map fun event => event.2.1).Nodup :=
    (permutation.map (fun event => event.2.1)).nodup_iff.mpr (by
      simpa only [List.map_map, Function.comp_def, transferEvent] using distinct)
  have noZero : ∀ event ∈ events, event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event member
    obtain ⟨edge, physical, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp member)
    obtain ⟨port, native, rfl⟩ := List.mem_map.mp physical
    exact port_not_zero cached row (by simpa using native)
  have observed := Delegation.Proofs.atomic_observations history aligned noZero initial actualDistinct
  intro port member
  have included := permutation.mem_iff.mpr (List.mem_map.mpr
    ⟨_, List.mem_map.mpr ⟨port, by simpa using member, rfl⟩, rfl⟩)
  obtain ⟨cell, _, address, read, _⟩ := observed _ included
  exact ⟨cell, address, read⟩

/-- Actual native equations and one initialized history execute the original
split call. Input observations and address distinctness are proved internally. -/
theorem native_call_executes_of_history (cached : Bool) (row : Row babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints cached fixedSetup))
    (active : row.assignment (row.columns cached).execute = 1)
    (index : Fin 361) {before after : State} (arguments : ArgumentsAt index.val before)
    (boundedReads : ∀ port ∈ row.ports cached, (readToken row.assignment port).word.Bounded)
    {cells : List Cell} {events : List MemoryAccess}
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((row.memorySteps cached).map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (initial : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before) :
    Call.Executes row.kind before after :=
  native_call_executes cached row holds active index arguments boundedReads history permutation
    (native_call_input_observations cached row holds active index arguments boundedReads
      history permutation aligned initial)

end Airbender.Keccak.Split.Native.Proofs
