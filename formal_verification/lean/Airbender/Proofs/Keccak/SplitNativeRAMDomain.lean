import Airbender.Proofs.Keccak.SplitNativeInputObservations
import Airbender.Proofs.ExternalBoundary.WorkerRAM

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem ports_ram_domain {n : Nat} (w : Nat → ZMod babyBearModulus)
    (pointer : BitVec 32) (outside : ROM.limit ≤ pointer.toNat) (aligned : pointer.toNat % 256 = 0)
    (ports : Array MemoryPort) (control pointerPort : MemoryPort)
    (lanes : Fin n → Bool → MemoryPort) (slot : Fin n → Fin 31)
    (enumeration : ports.toList = [control, pointerPort] ++
      (List.finRange n).flatMap fun lane => [lanes lane false, lanes lane true])
    (controlAddress : control.address.code w = (Cell.register 10).addressCode)
    (pointerAddress : pointerPort.address.code w = (Cell.register 11).addressCode)
    (laneAddress : ∀ lane high, (lanes lane high).address.code w =
      (Call.laneCell pointer (slot lane) high).addressCode) :
    ∀ port ∈ ports, ∃ location : ExternalBoundary.WorkerRAM.Location,
      port.address.code w = location.cell.addressCode := by
  have domain (lane : Fin n) (high : Bool) : ∃ location : ExternalBoundary.WorkerRAM.Location,
      (lanes lane high).address.code w = location.cell.addressCode := by
    let address := pointer + BitVec.ofNat 32 (8 * (slot lane).val + if high then 4 else 0)
    have lower : ROM.limit ≤ address.toNat := by
      dsimp only [address]
      rw [Call.Proofs.lane_address_value pointer aligned (slot lane) high]
      omega
    exact ⟨.ram address lower, laneAddress lane high⟩
  intro port included
  have member : port ∈ ports.toList := by simpa using included
  rw [enumeration] at member
  rcases List.mem_append.mp member with registers | indirect
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at registers
    rcases registers with rfl | rfl
    · exact ⟨.register 10, controlAddress⟩
    · exact ⟨.register 11, pointerAddress⟩
  · obtain ⟨lane, _, present⟩ := List.mem_flatMap.mp indirect
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact domain lane false
    · exact domain lane true

variable [Fact babyBearModulus.Prime]

/-- Supported control and pointer registers locate every actual native split
port in architectural registers or RAM above ROM. Lane values are not needed. -/
theorem native_call_ram_domain (cached : Bool) (row : Row babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints cached fixedSetup))
    (active : row.assignment (row.columns cached).execute = 1)
    (index : Fin 361) (before : State) (arguments : ArgumentsAt index.val before)
    (pointerBound : (readToken row.assignment (nativeRegisterPort cached row 1)).word.Bounded)
    (registers : ∀ register : Fin 2, ∃ cell : Cell,
      cell.addressCode = (nativeRegisterPort cached row register).address.code row.assignment ∧
        cell.read before = .ok (readToken row.assignment (nativeRegisterPort cached row register)).word.toBitVec before) :
    ∀ port ∈ row.ports cached, ∃ location : ExternalBoundary.WorkerRAM.Location,
      port.address.code row.assignment = location.cell.addressCode := by
  cases row with
  | mk kind w =>
    cases kind with
    | columnParity =>
      have equations : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
          (if cached then ColumnParityCached.clockConstraints columnParityFixedTable else
            ColumnParity.clockConstraints columnParityFixedTable) := by cases cached <;> exact holds
      have running : w 0 = 1 := by cases cached <;> exact active
      have control := parity_call_control_binding cached w equations running index before arguments (registers 0)
      obtain ⟨pointer, _, outside, aligned, word⟩ := parity_call_pointer_binding cached w index before arguments
        pointerBound (registers 1)
      apply ports_ram_domain w pointer outside aligned _ (parityControlPort cached) (parityPointerPort cached)
        (parityLanePort cached) (fun lane => (Call.slots index)[lane.val]) (parity_ports_enumeration cached w)
        (by cases cached <;> rfl) (by cases cached <;> rfl)
      intro lane high
      exact parity_call_lane_address cached high w pointer aligned word index lane (control.2.2.2.1 lane)
    | thetaRho =>
      have equations : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
          (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable else
            ThetaRho.clockConstraints thetaRhoFixedTable) := by cases cached <;> exact holds
      have running : w 0 = 1 := by cases cached <;> exact active
      have control := theta_call_control_binding cached w equations running index before arguments (registers 0)
      obtain ⟨pointer, _, outside, aligned, word⟩ := theta_call_pointer_binding cached w index before arguments
        pointerBound (registers 1)
      apply ports_ram_domain w pointer outside aligned _ (thetaControlPort cached) (thetaPointerPort cached)
        (thetaLanePort cached) (fun lane => (Call.slots index)[lane.val]) (theta_ports_enumeration cached w)
        (by cases cached <;> rfl) (by cases cached <;> rfl)
      intro lane high
      exact theta_call_lane_address cached high w pointer aligned word index lane (control.2.2.2.1 lane)
    | chi5 =>
      have equations : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
          (if cached then Chi5Cached.clockConstraints chi5FixedTable else
            Chi5.clockConstraints chi5FixedTable) := by cases cached <;> exact holds
      have running : w 0 = 1 := by cases cached <;> exact active
      have control := chi5_call_control_binding cached w equations running index before arguments (registers 0)
      obtain ⟨pointer, _, outside, aligned, word⟩ := chi5_call_pointer_binding cached w index before arguments
        pointerBound (registers 1)
      apply ports_ram_domain w pointer outside aligned _ (chi5ControlPort cached) (chi5PointerPort cached)
        (chi5LanePort cached) (fun lane => (Call.slots index)[lane.val]) (chi5_ports_enumeration cached w)
        (by cases cached <;> rfl) (by cases cached <;> rfl)
      intro lane high
      exact chi5_call_lane_address cached high w pointer aligned word index lane (control.2.2.2 lane)

end Airbender.Keccak.Split.Native.Proofs
