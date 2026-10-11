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

/-- A complete initialized request writes Clean's original Keccak permutation
    into actual Sail RAM. `WordMapping` exposes public x11 and successful
    initial/final lane reads; matching derives all ranges, scratch behavior
    and intermediate states. Caller request matching and modeled-table fidelity
    remain explicit boundaries of `CallInputs` and `tables`. -/
theorem Native.permutation_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : Reference.RiscV.Sail.State) (pointer : BitVec 32) (input output : Vector Nat 25),
      Permutation.WordMapping initial after pointer input output ∧
        Permutation.TraceMapping data initial after cells ∧ output = Specs.Keccak256.keccakPermutation input :=
  Proofs.permutation_binding hp inverse accepted inputs tables aligned

/-- One initialized 649-call span finishes with x10 = 1544. The imported
    equations and shared memory matching derive the entire control sequence;
    `inputs` supplies only the public start and request-span boundaries. -/
theorem call_control_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells) :
    CallControl data :=
  Proofs.call_control hp accepted inputs

/-- Every call has the expected control in native-clock order and retains
    the public pointer. All native accesses execute in actual Sail memory,
    and every lane effect matches the existing Clean operation reference.
    `permutation_soundness` composes these physical writes into the complete
    permutation; caller instructions and request matching remain separate. -/
theorem Native.call_execution [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data initial cells ∧ CallSchedule data ∧ CallPointer data initial ∧
      ∀ row ∈ data.rows, Native.RowEffects row.assignment :=
  Proofs.call_execution hp inverse accepted inputs tables aligned

/-- All calls retain the same public x11 pointer. Its value and native
    port mappings follow from initialized readonly history, not assumptions. -/
theorem call_pointer_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells) :
    CallPointer data initial :=
  Proofs.call_pointer hp accepted inputs

/-- Keccak's modeled controller selects physical lane addresses and controls
    actual initialized Sail transfers in a mixed delegation pool. All seven lane modes
    use the existing Clean references on native observations. No pointer/read/range/result
    premise is supplied. Caller binding remains open. -/
theorem Native.operation_execution [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Delegation.OperationInputs data before cells Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .keccak → Native.RowEffects row.assignment :=
  Native.Proofs.operation_execution hp inverse accepted inputs aligned

/-- Initialized native history supplies all read/write/terminal word bounds
    across the seven active modes. `inputs` retains public Sail initialization,
    native timestamp-offset room and modeled setup; it supplies no limb bounds.
    Call scheduling, physical column selection and ABI execution remain separate. -/
theorem Memory.native_value_bounds [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Memory.Inputs data before cells control) :
    (∀ row ∈ data.rows, ∀ port ∈ row.ports, (Trace.readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ data.rows, ∀ port ∈ row.ports, (row.writeToken port).word.Bounded) ∧
    (∀ token ∈ data.terminal, token.word.Bounded) :=
  Memory.Proofs.value_bounds hp accepted inputs

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

/-- An incoming x10 control and five actual state reads determine one Iota
    column and its Theta-C parity. Round zero is the initial parity pass;
    rounds 1–24 use Clean's original Iota constants. The imported equations
    derive selectors, byte bounds and every write. Call scheduling and global
    memory transport remain outside this local claim. -/
theorem iota_column_soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    {state : Vector Nat 25} {column : Fin 5} {round : Fin 25}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (mapping : IotaMapping state column round w) : IotaResult state column round w :=
  Proofs.iota_column hp holds mapping

/-- Two native calls produce all five Theta D lanes from Clean's original
    reference. The control write selects the next mode; actual lane transfers
    connect the calls. Lookups derive all input/result bounds, including copied
    limbs. Global memory and schedule enforcement are separate obligations. -/
theorem mix_columns_soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {first second : Nat → ZMod p}
    {c : Vector Nat 5} {round : Fin 32}
    (firstHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment first)
      (importedConstraints (setupTable control)))
    (secondHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment second)
      (importedConstraints (setupTable control)))
    (mapping : MixMapping c round first second) : MixResult c first second :=
  Proofs.mixed_columns hp firstHolds secondHolds mapping

/-- The native Theta writes supply every Rho input limb. Both imported rows
    determine the rotated writes of Clean's `rhoPi` and preserve the scratch lane.
    There is no caller-supplied range or expected-result premise. `mapping` leaves
    global column scheduling and memory matching visible as separate work. -/
theorem theta_rho_column_soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {theta rho : Nat → ZMod p}
    {state : Vector Nat 25} {d : Vector Nat 5} {column : Fin 5} {round : Fin 24}
    (thetaHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment theta)
      (importedConstraints (setupTable control)))
    (rhoHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment rho)
      (importedConstraints (setupTable control)))
    (mapping : ThetaRhoMapping state d column round theta rho) : RhoResult state d column rho :=
  Proofs.theta_rho_column hp thetaHolds rhoHolds mapping

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
