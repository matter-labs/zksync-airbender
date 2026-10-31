import Airbender.Review.Compiler.LookupArgument
import Airbender.Review.Compiler.NativeRow
import Airbender.Import.Compiler.Rows.WordMemoryUncached

namespace Airbender.Compiler.PooledRowNative.WordMemoryUncached
open Airbender Airbender.Compiler

/-- Nonzero physical generic/range16 requests belong to their independently
interpreted setup columns. This predicate is a consequence of LookupArguments. -/
def PhysicalAuthoredLookupValid (physical : GKRAddress → Source.BaseField) : Prop :=
  (∀ query ∈ Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.genericQueries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.Contains Airbender.Compiler.TableNative.WordMemoryUncached.native.genericSetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement))))
  ∧ (∀ query ∈ Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16Queries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.Contains Airbender.Compiler.TableNative.WordMemoryUncached.native.range16SetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement))))

/-- Source-projected logical operands at the physical source, borrow and
history coordinates. The public lookup argument matches nativeRequests; the
supporting proof transports that matching to this source interpretation. -/
noncomputable def physicalRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.genericQueries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement)),
    Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16Queries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.WordMemoryUncached.native.sourcePlacement)),
    Airbender.Compiler.HelperNative.WordMemoryUncached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.HelperNative.WordMemoryUncached.native.placement.project
        (input.physical ∘ Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.address))] 1)]).get group

/-- Expanded native lookup operands before alpha compression. The encodings and
masks are independently imported from the consumed native leaves; timestamp
recipes retain the physical borrow and memory-history coordinates. -/
noncomputable def nativeOperands (input : Input) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  ([[(15, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf15.weight.value input.physical)),
      (10, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf10.weight.value input.physical))],
      [(14, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf14.weight.value input.physical)),
      (0, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf0.weight.value input.physical)),
      (12, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf12.weight.value input.physical))],
      [(2, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf2.weight.value input.physical)),
      (4, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf4.weight.value input.physical)),
      (5, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf5.weight.value input.physical)),
      (6, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf6.weight.value input.physical)),
      (7, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf7.weight.value input.physical)),
      (8, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf8.weight.value input.physical)),
      (9, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf9.weight.value input.physical)),
      (13, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.leaf13.weight.value input.physical))]]).get group

def nativeSetupLeaf (group : Fin 3) : Nat :=
  ([11,
      1,
      3]).get group

noncomputable def nativeRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  (nativeOperands input group).map Prod.snd
-- End expanded native lookup operands.

/-- Exact matching of every enabled emitted tuple against the corresponding
literal setup columns. The generic Review definition states exact matching;
this generated binding selects the three setup-column groups and native tuples. -/
def LookupArguments (input : Input) : Type :=
  GroupedLookupArguments
    (fun group : Fin 3 => Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.fields
      (([Airbender.Compiler.TableNative.WordMemoryUncached.native.genericSetupColumns,
         Airbender.Compiler.TableNative.WordMemoryUncached.native.range16SetupColumns,
         Airbender.Compiler.TableNative.WordMemoryUncached.native.timestampSetupColumns]).get group))
    (fun group => activeLookupFields (nativeRequests input group))

/-- Match the same native tuples against independently supplied setup rows.
The calling boundary must bind these rows to public text and fixed setup data. -/
def LookupArgumentsWith
    (tables : Fin 3 → Fin Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.imported.data.length →
      List Source.BaseField) (input : Input) : Type :=
  GroupedLookupArguments tables (fun group => activeLookupFields (nativeRequests input group))

/-- The retained setup gives exactly the existing lookup argument type. -/
theorem lookup_arguments_with_retained (input : Input) :
    LookupArgumentsWith
      (fun group : Fin 3 => Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model.fields
        (([Airbender.Compiler.TableNative.WordMemoryUncached.native.genericSetupColumns,
           Airbender.Compiler.TableNative.WordMemoryUncached.native.range16SetupColumns,
           Airbender.Compiler.TableNative.WordMemoryUncached.native.timestampSetupColumns]).get group)) input =
      LookupArguments input := rfl
-- End generated logical lookup argument.

def inputRow (input : Input) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.wordMemory, (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement index)) input.physical)⟩

end Airbender.Compiler.PooledRowNative.WordMemoryUncached
