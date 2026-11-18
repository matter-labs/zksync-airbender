module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.NativeMemoryWorkers
public import Proven.GKRProtocol.Functional

@[expose] public section
set_option warningAsError true

/-! A functional program evaluates the extension caches and gates of a capture, layer by layer. Its
values meet the extension semantics of `NativeMemory`. The witnesses of the worker memory claims use it. -/

namespace Airbender.Compiler.NativeMemoryBridge
open NativeArithmetic NativeMemory

deriving instance DecidableEq for AffineProgram
deriving instance DecidableEq for RExpression

/-- `maskProduct mask input` as a functional expression. -/
def maskExpression (input mask : GKRAddress) : RExpression :=
  .add (.mul (.add (.input input) (.neg (.coefficient (.natural 1)))) (.input mask)) (.coefficient (.natural 1))

/-- The extension value of a cache. Scalar caches are base-field wires. -/
def cacheEntry (entry : GKRAddress × GKRCacheRelation) : Option (GKRAddress × RExpression) :=
  match entry.2 with
  | .MemoryTuple row => (tupleProgram row).map fun program => (entry.1, .affine program)
  | .VectorizedLookup row => some (entry.1, .affine (vectorProgram row))
  | .VectorizedLookupSetup addresses => some (entry.1, .affine (setupProgram addresses))
  | .SingleColumnLookup _ _ => none

/-- The extension value of a copy, a vector materialization or a RAM-product gate. -/
def gateEntry : GKRRelation → Option (GKRAddress × RExpression)
  | .CopyInExtensionField input output => some (output, .input input)
  | .MaterializedVectorLookupInput row output => some (output, .affine (vectorProgram row))
  | .InitialGrandProductFromCaches input output => match input.values.toList with
    | [left, right] => some (output, .mul (.input left) (.input right))
    | _ => none
  | .TrivialProduct input output => match input.values.toList with
    | [left, right] => some (output, .mul (.input left) (.input right))
    | _ => none
  | .InitialGrandProductWithoutCaches input output => match input.values.toList with
    | [left, right] => do some (output, .mul (.affine (← tupleProgram left)) (.affine (← tupleProgram right)))
    | _ => none
  | .MaterializeGrandProductTermExpression input output => (tupleProgram input).map fun program => (output, .affine program)
  | .MaskIntoIdentityProduct input mask output => some (output, maskExpression input mask)
  | _ => none

/-- The entries whose inputs are base wires or earlier outputs. -/
def readyEntries (roles : GKRAddress → Bool) (known : List GKRAddress)
    (entries : List (GKRAddress × RExpression)) : List (GKRAddress × RExpression) :=
  entries.filter fun entry => entry.2.inputs.all fun address => isBase roles address || known.contains address

/-- Each layer gives one step for its caches, then one step for its gates. -/
def extensionSteps (roles : GKRAddress → Bool) : List GKRLayerDescription → List GKRAddress → FunctionalProgram
  | [], _ => []
  | layer :: rest, known =>
    let caches := readyEntries roles known (layer.cached_relations.toList.filterMap cacheEntry)
    let afterCaches := caches.map Prod.fst ++ known
    let gates := readyEntries roles afterCaches
      ((layer.gates ++ layer.gates_with_external_connections).toList.filterMap fun gate =>
        gateEntry gate.enforced_relation)
    caches :: gates :: extensionSteps roles rest (gates.map Prod.fst ++ afterCaches)

def extensionProgram (roles : GKRAddress → Bool) (circuit : Circuit) : FunctionalProgram :=
  extensionSteps roles circuit.layers.toList []

/-- Every extension cache and gate is a program entry. A copy outside the program reads and writes
    no program output. -/
def programCovered (roles : GKRAddress → Bool) (circuit : Circuit) : Bool :=
  let program := extensionProgram roles circuit
  let entries := program.flatten
  let outputs := program.outputs
  (layerCaches circuit).all (fun entry => match cacheEntry entry with
    | none => true
    | some value => entries.contains value) &&
  (layerGates circuit).all fun gate => match gate.enforced_relation, gateEntry gate.enforced_relation with
    | .CopyInExtensionField input output, some value =>
      entries.contains value || (!outputs.contains input && !outputs.contains output)
    | _, none => true
    | _, some value => entries.contains value

variable {R : Type} [CommRing R]

/-- The extension values of the program, from base values and zero extension values. -/
noncomputable def programValues (roles : GKRAddress → Bool) (circuit : Circuit) (challenges : NativeMemory.Challenges R)
    (physical : GKRAddress → F) : GKRAddress → R :=
  (extensionProgram roles circuit).execute challenges.memory.embed (cacheChallenges challenges) 0 (isBase roles)
    (challenges.memory.embed ∘ physical) (fun _ => 0)

theorem program_frame (hom : Source.BaseField →+* R) (cache : CacheChallenges R) (gamma : R)
    (isBaseWire : GKRAddress → Bool) (base : GKRAddress → R) :
    ∀ (program : FunctionalProgram) (extension : GKRAddress → R) (address : GKRAddress),
      address ∉ program.outputs →
      program.execute hom cache gamma isBaseWire base extension address = extension address
  | [], _, _, _ => rfl
  | step :: rest, extension, address, outside => by
    simp only [FunctionalProgram.outputs, List.flatMap_cons, List.mem_append, not_or] at outside
    simp only [FunctionalProgram.execute]
    rw [program_frame hom cache gamma isBaseWire base rest _ address outside.2]
    apply Functional.write_frame
    simpa only [List.map_map, Function.comp_def, FunctionalStep.outputs] using outside.1

section Witness
variable (challenges : NativeMemory.Challenges R) (roles : GKRAddress → Bool) (physical : GKRAddress → F)
  {circuit : Circuit}

theorem program_wires : wires challenges roles physical (programValues roles circuit challenges physical) =
    Functional.read (isBase roles) (challenges.memory.embed ∘ physical)
      ((extensionProgram roles circuit).execute challenges.memory.embed (cacheChallenges challenges) 0 (isBase roles)
        (challenges.memory.embed ∘ physical) (fun _ => 0)) := rfl

/-- The program values meet the extension semantics of every cache and gate. -/
theorem program_holds (valid : (extensionProgram roles circuit).check (isBase roles) [] = true)
    (complete : programCovered roles circuit = true) (typed : typingChecked roles circuit = true) :
    NativeMemory.Holds circuit challenges physical (programValues roles circuit challenges physical) := by
  have sound := (FunctionalProgram.execute_sound (FunctionalProgram.check_sound valid) challenges.memory.embed
    (cacheChallenges challenges) 0 (challenges.memory.embed ∘ physical) (fun _ => 0)).1
  have entryHolds (entry : GKRAddress × RExpression) (member : (extensionProgram roles circuit).flatten.contains entry = true) :
      wires challenges roles physical (programValues roles circuit challenges physical) entry.1 =
        entry.2.value challenges.memory.embed (cacheChallenges challenges) 0
          (wires challenges roles physical (programValues roles circuit challenges physical)) := by
    obtain ⟨step, stepMember, inside⟩ := List.mem_flatten.mp (List.contains_iff_mem.mp member)
    exact sound step stepMember entry inside
  simp only [programCovered, Bool.and_eq_true, List.all_eq_true] at complete
  intro layer layerMember
  constructor
  · intro entry inside
    have cacheMember : entry ∈ layerCaches circuit :=
      List.mem_flatMap.mpr ⟨layer, Array.mem_def.mp layerMember, Array.mem_def.mp inside⟩
    have covered := complete.1 entry cacheMember
    have entryTyped := typed_caches roles typed entry cacheMember
    rcases entry with ⟨output, relation⟩
    cases relation with
    | SingleColumnLookup row width => trivial
    | MemoryTuple row =>
      simp only [cacheTyped, Bool.and_eq_true, Bool.not_eq_true', Option.isSome_iff_exists] at entryTyped
      obtain ⟨program, found⟩ := entryTyped.2
      simp only [cacheEntry, found, Option.map_some] at covered
      have holds := entryHolds _ covered
      simp only [RExpression.value, wires_extension challenges roles physical _ entryTyped.1] at holds
      have same := tuple_interpret challenges roles physical (programValues roles circuit challenges physical) row
      rw [found, Option.map_some] at same
      simp only [NativeMemory.CacheHolds, ← same, holds]
    | VectorizedLookup row =>
      simp only [cacheTyped, Bool.and_eq_true, Bool.not_eq_true'] at entryTyped
      simp only [cacheEntry] at covered
      have holds := entryHolds _ covered
      simp only [RExpression.value, wires_extension challenges roles physical _ entryTyped.1] at holds
      simp only [NativeMemory.CacheHolds, holds]
      exact vector_interpret challenges roles physical _ row entryTyped.2
    | VectorizedLookupSetup addresses =>
      simp only [cacheTyped, Bool.and_eq_true, Bool.not_eq_true'] at entryTyped
      simp only [cacheEntry] at covered
      have holds := entryHolds _ covered
      simp only [RExpression.value, wires_extension challenges roles physical _ entryTyped.1] at holds
      simp only [NativeMemory.CacheHolds, holds]
      exact setup_interpret challenges roles physical _ addresses entryTyped.2
  · intro gate inside
    have gateMember : gate ∈ layerGates circuit :=
      List.mem_flatMap.mpr ⟨layer, Array.mem_def.mp layerMember, Array.mem_def.mp inside⟩
    have covered := complete.2 gate gateMember
    have gateTyped' := typed_gates roles typed gate gateMember
    revert covered gateTyped'
    cases gate.enforced_relation <;> intro covered gateTyped' <;> simp only [NativeMemory.GateHolds]
    case CopyInExtensionField input output =>
      simp only [gateTyped, Bool.and_eq_true, Bool.not_eq_true'] at gateTyped'
      simp only [gateEntry, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at covered
      rcases covered with covered | ⟨inputOutside, outputOutside⟩
      · have holds := entryHolds _ covered
        simp only [RExpression.value, wires_extension challenges roles physical _ gateTyped'.1,
          wires_extension challenges roles physical _ gateTyped'.2] at holds
        exact holds
      · have outputAbsent : output ∉ (extensionProgram roles circuit).outputs := by simpa using outputOutside
        have inputAbsent : input ∉ (extensionProgram roles circuit).outputs := by simpa using inputOutside
        simp only [programValues]
        rw [program_frame _ _ _ _ _ _ _ output outputAbsent, program_frame _ _ _ _ _ _ _ input inputAbsent]
    case MaterializedVectorLookupInput row output =>
      simp only [gateTyped, Bool.and_eq_true, Bool.not_eq_true'] at gateTyped'
      simp only [gateEntry] at covered
      have holds := entryHolds _ covered
      simp only [RExpression.value, wires_extension challenges roles physical _ gateTyped'.1] at holds
      rw [holds]
      exact vector_interpret challenges roles physical _ row gateTyped'.2
    case InitialGrandProductFromCaches input output =>
      obtain ⟨left, right, pair⟩ := fixed_two input
      simp only [gateTyped, pair, Bool.and_eq_true, Bool.not_eq_true', List.all_cons, List.all_nil,
        Bool.and_true] at gateTyped'
      simp only [gateEntry, pair] at covered
      have holds := entryHolds _ covered
      simp only [RExpression.value, wires_extension challenges roles physical _ gateTyped'.1,
        wires_extension challenges roles physical _ gateTyped'.2.1,
        wires_extension challenges roles physical _ gateTyped'.2.2] at holds
      simp only [pair]
      exact holds
    case TrivialProduct input output =>
      obtain ⟨left, right, pair⟩ := fixed_two input
      simp only [gateTyped, pair, Bool.and_eq_true, Bool.not_eq_true', List.all_cons, List.all_nil,
        Bool.and_true] at gateTyped'
      simp only [gateEntry, pair] at covered
      have holds := entryHolds _ covered
      simp only [RExpression.value, wires_extension challenges roles physical _ gateTyped'.1,
        wires_extension challenges roles physical _ gateTyped'.2.1,
        wires_extension challenges roles physical _ gateTyped'.2.2] at holds
      simp only [pair]
      exact holds
    case InitialGrandProductWithoutCaches input output =>
      obtain ⟨left, right, pair⟩ := fixed_two input
      simp only [gateTyped, pair, Bool.and_eq_true, Bool.not_eq_true', List.all_cons, List.all_nil,
        Bool.and_true, Option.isSome_iff_exists] at gateTyped'
      obtain ⟨leftProgram, leftFound⟩ := gateTyped'.2.1
      obtain ⟨rightProgram, rightFound⟩ := gateTyped'.2.2
      simp only [gateEntry, pair, leftFound, rightFound, Option.bind_eq_bind, Option.bind_some] at covered
      have holds := entryHolds _ covered
      simp only [RExpression.value, wires_extension challenges roles physical _ gateTyped'.1] at holds
      have leftSame := tuple_interpret challenges roles physical (programValues roles circuit challenges physical) left
      have rightSame := tuple_interpret challenges roles physical (programValues roles circuit challenges physical) right
      rw [leftFound, Option.map_some] at leftSame
      rw [rightFound, Option.map_some] at rightSame
      simp only [pair]
      exact ⟨_, _, leftSame.symm, rightSame.symm, holds⟩
    case MaterializeGrandProductTermExpression input output =>
      simp only [gateTyped, Bool.and_eq_true, Bool.not_eq_true', Option.isSome_iff_exists] at gateTyped'
      obtain ⟨program, found⟩ := gateTyped'.2
      simp only [gateEntry, found, Option.map_some] at covered
      have holds := entryHolds _ covered
      simp only [RExpression.value, wires_extension challenges roles physical _ gateTyped'.1] at holds
      have same := tuple_interpret challenges roles physical (programValues roles circuit challenges physical) input
      rw [found, Option.map_some] at same
      rw [← same, holds]
    case MaskIntoIdentityProduct input mask output =>
      simp only [gateTyped, Bool.and_eq_true, Bool.not_eq_true'] at gateTyped'
      simp only [gateEntry] at covered
      have holds := entryHolds _ covered
      simp only [maskExpression, RExpression.value, coefficient_natural, Nat.cast_one, map_one,
        wires_extension challenges roles physical _ gateTyped'.1.1,
        wires_extension challenges roles physical _ gateTyped'.1.2,
        wires_base challenges roles physical _ gateTyped'.2] at holds
      rw [holds]
      simp only [PaddingBoundary.mask, Challenges.embed]
      ring

end Witness

end Airbender.Compiler.NativeMemoryBridge
