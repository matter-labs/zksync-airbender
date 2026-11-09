import Airbender.Review.Trace.Families.ReducedMachine.InitializationComponentTheorems

namespace Airbender.Tests.NativeInitializationComponent
open Airbender.NativeInactiveMain Airbender.NativeInitializationComponent Airbender.NativeInitializationComponentProofs
open Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
abbrev TestF := ZMod mersenne31Modulus

theorem original_scalar_constructor_exposed :
    NativeScalarTableCompletion.Fixture (NativeCSRPositiveWitness.assignment false) :=
  NativeScalarTableCompletionProofs.original_fixture

theorem original_existential_retained : ∃ w, NativeScalarTableCompletion.Fixture w := NativeScalarTableCompletionProofs.fixture

theorem both_original_records_zero (active : Bool) : NativeInitializationBoundary.record
    (NativeCSRPositiveWitness.assignment active) = Vector.replicate 6 0 := record_zero active

theorem all_ten_actual_queries_zero {R : Type} [Field R] (proof : NativeScalar16Arguments.Proof R)
    (rows : ∀ i,proof.initialization.main.rows i = NativeCSRPositiveWitness.assignment false)
    (i : Nat) (pair : Fin 5) (limb : Fin 2) : NativeScalar16Lookups.query proof i pair limb = 0 :=
  query_zero proof rows i pair limb

theorem logical_memberships_derived {R : Type} [Field R] (proof : NativeScalar16Arguments.Proof R)
    (rows : ∀ i,proof.initialization.main.rows i = NativeCSRPositiveWitness.assignment false) :
    NativeScalar16Lookups.LogicalLookups proof := logical_lookups proof rows

theorem constructed_setup_idempotent {R : Type} [Field R] (proof : NativeScalar16Arguments.Proof R) :
    NativePhysicalScalar16Setup.withPublicSetup (NativePhysicalScalar16Setup.withPublicSetup proof) =
      NativePhysicalScalar16Setup.withPublicSetup proof := public_setup_idempotent proof

theorem all_six_endpoint_fields (w : Nat → TestF) :
    NativeInitializationBoundary.EndpointAccepted w (NativeInitializationBoundary.record w) := endpoint_self w

def reservedRows (i : Nat) : Nat → TestF :=
  if i = scalar16Layout.traceLength-1 then (fun _ => 1) else NativeCSRPositiveWitness.assignment false

/-- Observer-only input, with no Accepted claim. -/
def reservedProbe {R : Type} [Field R] (proof : NativeScalar16Arguments.Proof R) : NativeScalar16Arguments.Proof R :=
  { proof with initialization := { proof.initialization with main := { proof.initialization.main with rows := reservedRows } } }

theorem reserved_row_is_not_public_endpoint {R : Type} [Field R] (proof : NativeScalar16Arguments.Proof R) :
    observedValues (reservedProbe proof) = zeroValues ∧
      NativeInitializationBoundary.record ((reservedProbe proof).initialization.main.rows (scalar16Layout.traceLength-1)) ≠ Vector.replicate 6 0 := by
  constructor
  · unfold observedValues reservedProbe
    change (⟨NativeInitializationBoundary.record (reservedRows 0),
      NativeInitializationBoundary.record (reservedRows (scalar16Layout.traceLength-2))⟩ : NativeInitializationBoundary.PublicValues) = zeroValues
    have first : reservedRows 0 = NativeCSRPositiveWitness.assignment false := if_neg (by decide)
    have last : reservedRows (scalar16Layout.traceLength-2) = NativeCSRPositiveWitness.assignment false := if_neg (by decide)
    rw [first,last,record_zero false]
    rfl
  · change NativeInitializationBoundary.record (reservedRows (scalar16Layout.traceLength-1)) ≠ _
    rw [reservedRows,if_pos rfl,(NativeInitializationBoundaryProofs.geometry _).1]
    decide +kernel

theorem wrong_raw_endpoint_time_rejected : ¬ NativeInitializationBoundary.EndpointAccepted
    (NativeCSRPositiveWitness.assignment false) #v[0,0,0,0,0,1] := by
  intro accepted
  have fields := NativeInitializationBoundaryProofs.endpoint accepted
  rw [record_zero false] at fields
  have wrong : (0 : TestF) = 1 := by simpa using congrArg (fun v : Vector TestF 6 => v[5]) fields
  exact zero_ne_one wrong

theorem zero_address_parses : NativeInitializationWindow.parseAddress (Vector.replicate 6 (0 : TestF)) = some 0 := by
  rw [NativeInitializationAddressParserProofs.parsed (by constructor <;> decide +kernel)]
  rfl

theorem complete_zero_window : NativeInitializationWindow.WindowAccepted zeroValues zeroValues := window_zero

theorem wrong_raw_fallback_time_rejected : ¬ NativeInitializationWindow.WindowAccepted
    ⟨Vector.replicate 6 0,#v[0,0,0,0,0,1]⟩ zeroValues := by
  have badParsed : NativeInitializationWindow.parseAddress #v[(0 : TestF),0,0,0,0,1] = some 0 := by
    rw [NativeInitializationAddressParserProofs.parsed (by constructor <;> decide +kernel)]
    rfl
  unfold NativeInitializationWindow.WindowAccepted zeroValues
  rw [badParsed,zero_address_parses]
  change ¬ ((0 : Nat) = 0 ∧ ∀ slot : Fin 4, (#v[(0 : TestF),0,0,0,0,1])[slot.val+2] = 0)
  intro accepted
  have wrong := accepted.2 3
  change (1 : TestF) = 0 at wrong
  exact one_ne_zero wrong

section Joined
variable {R : Type} [Field R] {embed : TestF →+* R} {memory : MemoryKeyChallenges R}
  {pc : PCChallenges R} {ch : CSRArgumentChallenges R} {decoder : NativeDecoderArguments.Challenges R}
  {gamma : R} {w : Nat → TestF} {before : MainProof R} {omega : R}
  {proof : NativeDecoderTableArguments.Proof R} {base : Nat → BaseAuxiliaryColumn → TestF}
  {witness : Nat → Scalar16WitnessColumn → TestF} {setup : Nat → Scalar16SetupColumn → TestF} {p : Polynomial R}
  (accepted : NativeInitializationComponent.Completion embed memory pc ch decoder gamma w before omega proof base witness setup p)
include accepted

theorem full_scalar_retained : NativeScalar16Arguments.Accepted embed memory pc gamma
    (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup p omega) := accepted.source.scalar

theorem full_caller_retained : CallerDelegationAccepted embed ch proof.main.caller := accepted.source.paired.decoder.caller.caller

theorem full_decoder_table_retained : NativeDecoderTableArguments.TableAccepted embed decoder proof := accepted.source.paired.decoder.table

theorem full_boundary_retained : NativeInitializationBoundary.Accepted embed memory pc gamma
    (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup p omega)
    (observedValues (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup p omega)) := accepted.boundary

theorem every_finite_copy_window (count : Nat) : NativeInitializationWindow.Accepted embed memory pc gamma count
    (fun _ => chunk (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup p omega)) := accepted.repeated count

theorem every_ordinary_padding : ∀ i < scalar16Layout.traceLength-1,
    NativeInitializationOrdering.PaddingRecord (proof.main.memory.rows i) := accepted.padding

theorem all_twelve_endpoint_relations :
    NativeInitializationBoundary.EndpointAccepted
      ((NativeScalarTableCompletion.scalarView gamma proof.main base witness setup p omega).initialization.main.rows 0)
      (observedValues (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup p omega)).first ∧
    NativeInitializationBoundary.EndpointAccepted
      ((NativeScalarTableCompletion.scalarView gamma proof.main base witness setup p omega).initialization.main.rows (scalar16Layout.traceLength-2))
      (observedValues (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup p omega)).oneBeforeLast :=
  ⟨accepted.boundary.first,accepted.boundary.oneBeforeLast⟩

theorem all_four_public_address_bounds :
    (observedValues (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup p omega)).first[0].val < 65536 ∧
    (observedValues (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup p omega)).first[1].val < 65536 ∧
    (observedValues (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup p omega)).oneBeforeLast[0].val < 65536 ∧
    (observedValues (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup p omega)).oneBeforeLast[1].val < 65536 :=
  NativeInitializationBoundaryProofs.public_bounds embed memory pc gamma accepted.boundary
end Joined

theorem original_joint_constructor : NativeInitializationComponent.Fixture (NativeCSRPositiveWitness.assignment false) :=
  NativeInitializationComponentProofs.original_fixture

theorem full_joint_fixture : ∃ w, NativeInitializationComponent.Fixture w := native_inactive_initialization_component
end Airbender.Tests.NativeInitializationComponent
