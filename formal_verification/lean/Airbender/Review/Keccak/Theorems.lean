import Airbender.Proofs.Keccak.Theta
import Airbender.Proofs.Keccak.Chi
import Airbender.Proofs.Keccak.Addresses
import Airbender.Proofs.Keccak.FixedLookups
import Airbender.Proofs.Keccak.ControlUpdate
import Airbender.Proofs.BabyBear

namespace Airbender.Keccak

/-- Local control well-formedness and pointer alignment
    from the actual no-cache artifact, for any supplied fixed setup.
    This does not yet claim lane-operation or permutation soundness. -/
theorem local_checks {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p)
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

/-- Conditional soundness of one active Theta column, with actual native writes.
    The interface binds memory reads; no result, byte or word bound is assumed. -/
theorem theta_column_soundness {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    {state : Vector Nat 25} {d : Vector Nat 5} {column : Fin 5}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (interface : ThetaInterface state d column w) : ThetaResult state d column w :=
  Proofs.theta_column hp holds interface

/-- The two native Chi modes produce one complete five-lane row of Clean's
    original reference. `mapping` connects state reads and scratch transfers;
    imported equations and modeled lookups determine every write, without range
    or expected-result premises. Scheduling and global memory transport are separate. -/
theorem chi_row_soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {first second : Nat → ZMod p}
    {state : Vector Nat 25} {row : Fin 5}
    (firstHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment first)
      (importedConstraints (setupTable control)))
    (secondHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment second)
      (importedConstraints (setupTable control)))
    (mapping : ChiMapping state row first second) : ChiResult state row first second :=
  Proofs.chi_row hp firstHolds secondHolds mapping

/-- The supplied setup ranges lane indices; native equations and queries derive
    alignment and address interpretation. Global memory enforcement is external. -/
theorem address_checks {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (rowsBounded : ∀ key : Fin 4096, ∀ i : Fin 6, (control key)[i] < 31)
    (pointerBounded : (statePointer w).Bounded)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) : AddressChecks w :=
  Proofs.addresses hp inverse rowsBounded pointerBounded holds

/-- Exact, bounded fixed-table relations for every native byte query. Rust setup
    binding and assembly into the remaining lane modes are separate obligations. -/
theorem fixed_lookup_checks {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) : ByteLookupChecks control w :=
  Proofs.byte_lookup_checks hp holds

/-- Actual x10 updates, including loop/round rollover and inactive preservation.
    No controller-table contents or decoded-control premise is required. -/
theorem control_updates {p : Nat} [Fact p.Prime] (hp : 4096 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) : ControlUpdateChecks w :=
  Proofs.control_update_checks hp holds

end Airbender.Keccak
