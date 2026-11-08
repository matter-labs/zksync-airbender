module
public import Slop.Keccak.NativeExecution
public import Slop.Keccak.ControlHistory
public import Slop.Keccak.PointerHistory
public import Slop.Keccak.Theta
public import Slop.Keccak.Chi
public import Slop.Keccak.Iota
public import Slop.Keccak.Mix
public import Slop.Keccak.Rho
public import Slop.Keccak.Addresses
public import Slop.Keccak.FixedLookups
public import Slop.Keccak.ControlUpdate
public import Human.Helpers.Delegation.SpanABI
public import Human.Trace.Workers.Blake2G.WorkVector
public import Slop.Delegation.NativeSegments
public import Slop.Keccak.CallPermutation

@[expose] public section

namespace Airbender.Keccak


theorem local_checks {p : Nat} [Fact p.Prime] (hp : 134217728 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) : LocalChecks w :=
  Proofs.local_checks hp inverse holds

theorem babyBear_local_checks {setup : Table (ZMod babyBearModulus) (fields 8)}
    {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) : LocalChecks w :=
  local_checks (by decide) (by decide) holds


theorem theta_column_soundness {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    {state : Vector Nat 25} {d : Vector Nat 5} {column : Fin 5}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (interface : ThetaInterface state d column w) : ThetaResult state d column w :=
  Proofs.theta_column hp holds interface


theorem chi_row_soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {first second : Nat → ZMod p}
    {state : Vector Nat 25} {row : Fin 5}
    (firstHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment first)
      (importedConstraints (setupTable control)))
    (secondHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment second)
      (importedConstraints (setupTable control)))
    (mapping : ChiMapping state row first second) : ChiResult state row first second :=
  Proofs.chi_row hp firstHolds secondHolds mapping


theorem iota_column_soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    {state : Vector Nat 25} {column : Fin 5} {round : Fin 25}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (mapping : IotaMapping state column round w) : IotaResult state column round w :=
  Proofs.iota_column hp holds mapping


theorem mix_columns_soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {first second : Nat → ZMod p}
    {c : Vector Nat 5} {round : Fin 32}
    (firstHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment first)
      (importedConstraints (setupTable control)))
    (secondHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment second)
      (importedConstraints (setupTable control)))
    (mapping : MixMapping c round first second) : MixResult c first second :=
  Proofs.mixed_columns hp firstHolds secondHolds mapping


theorem theta_rho_column_soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {theta rho : Nat → ZMod p}
    {state : Vector Nat 25} {d : Vector Nat 5} {column : Fin 5} {round : Fin 24}
    (thetaHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment theta)
      (importedConstraints (setupTable control)))
    (rhoHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment rho)
      (importedConstraints (setupTable control)))
    (mapping : ThetaRhoMapping state d column round theta rho) : RhoResult state d column rho :=
  Proofs.theta_rho_column hp thetaHolds rhoHolds mapping


theorem address_checks {p : Nat} [Fact p.Prime] (hp : 134217728 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (rowsBounded : ∀ key : Fin 4096, ∀ i : Fin 6, (control key)[i] < 31)
    (pointerBounded : (statePointer w).Bounded)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) : AddressChecks w :=
  Proofs.addresses hp inverse rowsBounded pointerBounded holds


theorem fixed_lookup_checks {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) : ByteLookupChecks control w :=
  Proofs.byte_lookup_checks hp holds


theorem control_updates {p : Nat} [Fact p.Prime] (hp : 4096 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) : ControlUpdateChecks w :=
  Proofs.control_update_checks hp holds

end Airbender.Keccak
