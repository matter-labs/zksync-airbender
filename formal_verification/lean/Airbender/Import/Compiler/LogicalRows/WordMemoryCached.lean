import Airbender.Review.Compiler.LookupArgument
import Airbender.Review.Compiler.NativeRow
import Airbender.Import.Compiler.Rows.WordMemoryCached

namespace Airbender.Compiler.PooledRowNative.WordMemoryCached
open Airbender Airbender.Compiler

/-- Nonzero physical generic/range16 requests belong to their independently
interpreted setup columns. This predicate is a consequence of LookupArguments. -/
def PhysicalAuthoredLookupValid (physical : GKRAddress → Source.BaseField) : Prop :=
  (∀ query ∈ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.Contains Airbender.Compiler.TableNative.WordMemoryCached.native.genericSetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement))))
  ∧ (∀ query ∈ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.Contains Airbender.Compiler.TableNative.WordMemoryCached.native.range16SetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement))))

/-- Source-projected logical operands at the physical source, borrow and
history coordinates. The public lookup argument matches nativeRequests; the
supporting proof transports that matching to this source interpretation. -/
noncomputable def physicalRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)),
    Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement)),
    Airbender.Compiler.HelperNative.WordMemoryCached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.HelperNative.WordMemoryCached.native.placement.project
        (input.physical ∘ Airbender.Compiler.MemoryNative.WordMemoryCached.native.bank.address))] 1)]).get group

/-- Expanded native lookup operands before alpha compression. The encodings and
masks are independently imported from the consumed native leaves; timestamp
recipes retain the physical borrow and memory-history coordinates. -/
noncomputable def nativeOperands (input : Input) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  ([[(15, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf15.weight.value input.physical)),
      (10, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf10.weight.value input.physical))],
      [(14, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf14.weight.value input.physical)),
      (0, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf0.weight.value input.physical)),
      (12, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf12.weight.value input.physical))],
      [(2, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf2.weight.value input.physical)),
      (4, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf4.weight.value input.physical)),
      (5, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf5.weight.value input.physical)),
      (6, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf6.weight.value input.physical)),
      (7, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf7.weight.value input.physical)),
      (8, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf8.weight.value input.physical)),
      (9, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf9.weight.value input.physical)),
      (13, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf13.weight.value input.physical))]]).get group

def nativeSetupLeaf (group : Fin 3) : Nat :=
  ([11,
      1,
      3]).get group

noncomputable def nativeRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  (nativeOperands input group).map Prod.snd
-- End expanded native lookup operands.

/-- Exact matching of every enabled emitted tuple against the corresponding
literal setup columns. This is the retained logical argument boundary; sampled
field-sum equality is insufficient. Source membership and helper ranges are
consequences, not fields of this contract. -/
def LookupArguments (input : Input) : Type :=
  (group : Fin 3) → LookupArgument
    (Airbender.Compiler.MaterializedNative.WordMemoryCached.native.model.fields (([Airbender.Compiler.TableNative.WordMemoryCached.native.genericSetupColumns, Airbender.Compiler.TableNative.WordMemoryCached.native.range16SetupColumns, Airbender.Compiler.TableNative.WordMemoryCached.native.timestampSetupColumns]).get group))
    (activeLookupFields (nativeRequests input group))

def inputRow (input : Input) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.wordMemory, (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.placement index)) input.physical)⟩

end Airbender.Compiler.PooledRowNative.WordMemoryCached
