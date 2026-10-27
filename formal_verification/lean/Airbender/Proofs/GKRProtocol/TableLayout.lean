import Airbender.Review.Compiler.Setup
import Airbender.Proofs.GKRProtocol.SourceFields
import Airbender.Proofs.GKRProtocol.BaseEncoding

namespace Airbender.Compiler
set_option warningAsError true

/-- Table placement computed from the original table sizes and compilation
configuration. The native output does not supply these source sizes. -/
structure SourceTablePlan where
  sizes : List Nat
  decoderWords : Nat
  traceLog2 : Nat
  width : Nat
  includeTableIDs : Bool
  deriving DecidableEq

structure LookupTableLayout where
  offsets : List Nat
  decoderOffset : Nat
  totalSize : Nat
  traceLength : Nat
  width : Nat
  includeTableIDs : Bool
  deriving DecidableEq

def SourceTablePlan.offsets : List Nat → Nat → List Nat
  | [], _ => []
  | size :: rest, offset => offset :: offsets rest (offset + size)

def SourceTablePlan.layout (plan : SourceTablePlan) : LookupTableLayout :=
  ⟨offsets plan.sizes 0, plan.sizes.sum, plan.sizes.sum + plan.decoderWords,
    2 ^ plan.traceLog2, plan.width, plan.includeTableIDs⟩

theorem SourceTablePlan.offsets_length (sizes : List Nat) (initial : Nat) :
    (offsets sizes initial).length = sizes.length := by
  induction sizes generalizing initial with
  | nil => rfl
  | cons size rest proof => exact congrArg Nat.succ (proof (initial + size))

def SourceLookupSetupRow.value [CommRing R] (row : SourceLookupSetupRow)
    (hom : Source.BaseField →+* R) (alpha gamma : R) : RationalPair R :=
  RationalPair.leaf (-hom row.multiplicity)
    (NativeLookupEncoding.linearize hom alpha row.fields 0 0 + gamma)

theorem NativeLookupEncoding.source_setup_fields (encoding : NativeLookupEncoding)
    (columns : List SourceSetupColumn)
    (checked : encoding.columns = columns.map (fun column => .input column.address))
    (base : GKRAddress → Source.BaseField) (table : SourceSetupColumn → Source.BaseField)
    (cells : ∀ column ∈ columns, base column.address = table column) :
    encoding.fields base = columns.map table := by
  rw [NativeLookupEncoding.fields, checked, List.map_map]
  exact List.map_congr_left cells

/-- A scalar setup has one field; a generic setup retains its ordered vector
of source table columns. -/
def sourceSetupEncoding : OutputType → Nat → Option NativeLookupEncoding
  | .GenericLookup, width => some (.vector
      ((List.range width).map (fun column => .input (.Setup column))))
  | .Lookup16Bits, _ => some (.scalar (.input (.VirtualSetup .RangeCheck16Bits)))
  | .LookupTimestamps, _ => some (.scalar (.input (.VirtualSetup .RangeCheckTimestamp)))
  | .PermutationProduct, _ | .InitsAndTeardownsProduct, _ => none

theorem NativeLookupLeaf.source_setup [CommRing R] (leaf : NativeLookupLeaf)
    (encoding : NativeLookupEncoding) (typing : ConsumerTyping)
    (baseCheck : encoding.baseCheck typing = true) (definitions : List AffineDefinition) (indices : List Nat)
    (expanded : LookupPayload.expand definitions indices leaf.payload = some encoding.program)
    (assignment : TypedAssignment R) (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (defined : ∀ definition ∈ definitions, definition.Holds hom challenges (assignment.value typing hom))
    (row : SourceLookupSetupRow)
    (fields : encoding.fields assignment.base = row.fields)
    (multiplicity : leaf.weight.value (assignment.value typing hom) = -hom row.multiplicity) :
    leaf.value hom challenges gamma (assignment.value typing hom) = row.value hom challenges.lookupAlpha gamma := by
  have expansion := LookupPayload.expand_sound hom challenges (assignment.value typing hom) defined expanded
  have payload := expansion.symm.trans (encoding.interpret_typed typing baseCheck assignment hom challenges)
  rw [fields] at payload
  exact congrArg₂ RationalPair.mk multiplicity (congrArg (· + gamma) payload)

end Airbender.Compiler
