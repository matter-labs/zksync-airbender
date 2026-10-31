import Airbender.Review.Compiler.LookupArgument
import Airbender.Review.Compiler.NativeRow
import Airbender.Import.Compiler.Rows.SubwordMemoryUncached

namespace Airbender.Compiler.PooledRowNative.SubwordMemoryUncached
open Airbender Airbender.Compiler

/-- Nonzero physical generic/range16 requests belong to their independently
interpreted setup columns. This predicate is a consequence of LookupArguments. -/
def PhysicalAuthoredLookupValid (physical : GKRAddress → Source.BaseField) : Prop :=
  (∀ query ∈ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement))))
  ∧ (∀ query ∈ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.Contains Airbender.Compiler.TableNative.SubwordMemoryUncached.native.range16SetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement))))

/-- Source-projected logical operands at the physical source, borrow and
history coordinates. The public lookup argument matches nativeRequests; the
supporting proof transports that matching to this source interpretation. -/
noncomputable def physicalRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)),
    Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement)),
    Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.placement.project
        (input.physical ∘ Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank.address))] 1)]).get group

/-- Expanded native lookup operands before alpha compression. The encodings and
masks are independently imported from the consumed native leaves; timestamp
recipes retain the physical borrow and memory-history coordinates. -/
noncomputable def nativeOperands (input : Input) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  ([[(17, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf17.weight.value input.physical)),
      (18, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf18.weight.value input.physical)),
      (12, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf12.weight.value input.physical))],
      [(14, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf14.weight.value input.physical)),
      (0, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf0.weight.value input.physical)),
      (15, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf15.weight.value input.physical)),
      (2, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf2.weight.value input.physical)),
      (3, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf3.weight.value input.physical))],
      [(4, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf4.weight.value input.physical)),
      (6, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf6.weight.value input.physical)),
      (7, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf7.weight.value input.physical)),
      (8, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf8.weight.value input.physical)),
      (9, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf9.weight.value input.physical)),
      (10, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf10.weight.value input.physical)),
      (11, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf11.weight.value input.physical)),
      (16, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf16.weight.value input.physical))]]).get group

def nativeSetupLeaf (group : Fin 3) : Nat :=
  ([13,
      1,
      5]).get group

noncomputable def nativeRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  (nativeOperands input group).map Prod.snd
-- End expanded native lookup operands.

/-- Exact matching of every enabled emitted tuple against the corresponding
literal setup columns. The generic Review definition states exact matching;
this generated binding selects the three setup-column groups and native tuples. -/
def LookupArguments (input : Input) : Type :=
  GroupedLookupArguments
    (fun group : Fin 3 => Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.fields
      (([Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumns,
         Airbender.Compiler.TableNative.SubwordMemoryUncached.native.range16SetupColumns,
         Airbender.Compiler.TableNative.SubwordMemoryUncached.native.timestampSetupColumns]).get group))
    (fun group => activeLookupFields (nativeRequests input group))

/-- Match the same native tuples against independently supplied setup rows.
The calling boundary must bind these rows to public text and fixed setup data. -/
def LookupArgumentsWith
    (tables : Fin 3 → Fin Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.imported.data.length →
      List Source.BaseField) (input : Input) : Type :=
  GroupedLookupArguments tables (fun group => activeLookupFields (nativeRequests input group))

/-- The retained setup gives exactly the existing lookup argument type. -/
theorem lookup_arguments_with_retained (input : Input) :
    LookupArgumentsWith
      (fun group : Fin 3 => Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model.fields
        (([Airbender.Compiler.TableNative.SubwordMemoryUncached.native.genericSetupColumns,
           Airbender.Compiler.TableNative.SubwordMemoryUncached.native.range16SetupColumns,
           Airbender.Compiler.TableNative.SubwordMemoryUncached.native.timestampSetupColumns]).get group)) input =
      LookupArguments input := rfl
-- End generated logical lookup argument.

def inputRow (input : Input) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.subwordMemory, (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address
    (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.placement index)) input.physical)⟩

end Airbender.Compiler.PooledRowNative.SubwordMemoryUncached
