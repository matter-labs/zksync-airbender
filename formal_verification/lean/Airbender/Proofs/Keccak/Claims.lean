import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.Workers.Keccak.Theorems
import Airbender.Proofs.Keccak.NativeExecution
import Airbender.Proofs.Keccak.PermutationBinding
import Airbender.Proofs.Keccak.ControlHistory
import Airbender.Proofs.Keccak.CallExecution
import Airbender.Proofs.Keccak.PointerHistory
import Airbender.Proofs.Keccak.Theta
import Airbender.Proofs.Keccak.Chi
import Airbender.Proofs.Keccak.Iota
import Airbender.Proofs.Keccak.Mix
import Airbender.Proofs.Keccak.Rho
import Airbender.Proofs.Keccak.Addresses
import Airbender.Proofs.Keccak.FixedLookups
import Airbender.Proofs.Keccak.ControlUpdate
import Airbender.Proofs.Keccak.MemorySoundness
import Airbender.Proofs.BabyBear

namespace Airbender.Keccak


theorem call_control_soundness [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells) :
    CallControl data :=
  Proofs.call_control hp accepted inputs.toBoundaryInputs


theorem Native.call_execution [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (inverse : SerializedInverse.Scale256 p)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data initial cells ∧ CallSchedule data ∧ CallPointer data initial ∧
      ∀ row ∈ data.rows, Native.RowEffects row.assignment :=
  Proofs.call_execution hp inverse accepted inputs.toBoundaryInputs tables aligned


theorem call_pointer_soundness [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells) :
    CallPointer data initial :=
  Proofs.call_pointer hp accepted inputs.toBoundaryInputs


theorem Memory.native_value_bounds [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Memory.Inputs data before cells control) :
    (∀ row ∈ data.rows, ∀ port ∈ row.ports, (Trace.readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ data.rows, ∀ port ∈ row.ports, (row.writeToken port).word.Bounded) ∧
    (∀ token ∈ data.terminal, token.word.Bounded) :=
  Memory.Proofs.value_bounds hp accepted inputs


theorem local_checks {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (inverse : SerializedInverse.Scale256 p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) : LocalChecks w :=
  Proofs.local_checks hp inverse holds

theorem babyBear_local_checks {setup : Table (ZMod babyBearModulus) (fields 8)}
    {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) : LocalChecks w :=
  local_checks (by decide) (by decide) holds


theorem theta_column_soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    {state : Vector Nat 25} {d : Vector Nat 5} {column : Fin 5}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (interface : ThetaInterface state d column w) : ThetaResult state d column w :=
  Proofs.theta_column hp holds interface


theorem chi_row_soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {first second : Nat → ZMod p}
    {state : Vector Nat 25} {row : Fin 5}
    (firstHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment first)
      (importedConstraints (setupTable control)))
    (secondHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment second)
      (importedConstraints (setupTable control)))
    (mapping : ChiMapping state row first second) : ChiResult state row first second :=
  Proofs.chi_row hp firstHolds secondHolds mapping


theorem iota_column_soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    {state : Vector Nat 25} {column : Fin 5} {round : Fin 25}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (mapping : IotaMapping state column round w) : IotaResult state column round w :=
  Proofs.iota_column hp holds mapping


theorem mix_columns_soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {first second : Nat → ZMod p}
    {c : Vector Nat 5} {round : Fin 32}
    (firstHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment first)
      (importedConstraints (setupTable control)))
    (secondHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment second)
      (importedConstraints (setupTable control)))
    (mapping : MixMapping c round first second) : MixResult c first second :=
  Proofs.mixed_columns hp firstHolds secondHolds mapping


theorem theta_rho_column_soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {theta rho : Nat → ZMod p}
    {state : Vector Nat 25} {d : Vector Nat 5} {column : Fin 5} {round : Fin 24}
    (thetaHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment theta)
      (importedConstraints (setupTable control)))
    (rhoHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment rho)
      (importedConstraints (setupTable control)))
    (mapping : ThetaRhoMapping state d column round theta rho) : RhoResult state d column rho :=
  Proofs.theta_rho_column hp thetaHolds rhoHolds mapping


theorem address_checks {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (inverse : SerializedInverse.Scale256 p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (rowsBounded : ∀ key : Fin 4096, ∀ i : Fin 6, (control key)[i] < 31)
    (pointerBounded : (statePointer w).Bounded)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) : AddressChecks w :=
  Proofs.addresses hp inverse rowsBounded pointerBounded holds


theorem fixed_lookup_checks {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) : ByteLookupChecks control w :=
  Proofs.byte_lookup_checks hp holds


theorem control_updates {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 4096)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) : ControlUpdateChecks w :=
  Proofs.control_update_checks hp holds

end Airbender.Keccak
