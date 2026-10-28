import Airbender.Review.Compiler.LookupArgument
import Airbender.Review.Compiler.NativeRow
import Airbender.Import.Compiler.Rows.SubwordMemoryCached

namespace Airbender.Compiler.PooledRowNative.SubwordMemoryCached
open Airbender Airbender.Compiler

/-- Nonzero physical generic/range16 requests belong to their independently
interpreted setup columns. This predicate is a consequence of LookupArguments. -/
def PhysicalAuthoredLookupValid (physical : GKRAddress → Source.BaseField) : Prop :=
  (∀ query ∈ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.Contains Airbender.Compiler.TableNative.SubwordMemoryCached.native.genericSetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement))))
  ∧ (∀ query ∈ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.Contains Airbender.Compiler.TableNative.SubwordMemoryCached.native.range16SetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement))))

/-- Source-projected logical operands at the physical source, borrow and
history coordinates. The public lookup argument matches nativeRequests; the
supporting proof transports that matching to this source interpretation. -/
noncomputable def physicalRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)),
    Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.SubwordMemoryCached.native.sourcePlacement)),
    Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.placement.project
        (input.physical ∘ Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address))] 1)]).get group

/-- Expanded native lookup operands before alpha compression. The encodings and
masks are independently imported from the consumed native leaves; timestamp
recipes retain the physical borrow and memory-history coordinates. -/
noncomputable def nativeOperands (input : Input) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  ([[(17, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf17.weight.value input.physical)),
      (18, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf18.weight.value input.physical)),
      (12, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf12.weight.value input.physical))],
      [(14, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf14.weight.value input.physical)),
      (0, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf0.weight.value input.physical)),
      (15, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf15.weight.value input.physical)),
      (2, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf2.weight.value input.physical)),
      (3, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf3.weight.value input.physical))],
      [(4, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf4.weight.value input.physical)),
      (6, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf6.weight.value input.physical)),
      (7, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf7.weight.value input.physical)),
      (8, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf8.weight.value input.physical)),
      (9, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf9.weight.value input.physical)),
      (10, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf10.weight.value input.physical)),
      (11, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf11.weight.value input.physical)),
      (16, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.leaf16.weight.value input.physical))]]).get group

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
    (fun group : Fin 3 => Airbender.Compiler.MaterializedNative.SubwordMemoryCached.native.model.fields
      (([Airbender.Compiler.TableNative.SubwordMemoryCached.native.genericSetupColumns,
         Airbender.Compiler.TableNative.SubwordMemoryCached.native.range16SetupColumns,
         Airbender.Compiler.TableNative.SubwordMemoryCached.native.timestampSetupColumns]).get group))
    (fun group => activeLookupFields (nativeRequests input group))
-- End generated logical lookup argument.

def inputRow (input : Input) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.subwordMemory, (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address
    (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.placement index)) input.physical)⟩

end Airbender.Compiler.PooledRowNative.SubwordMemoryCached
