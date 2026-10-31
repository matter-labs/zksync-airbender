import Airbender.Review.Compiler.LookupArgument
import Airbender.Review.Compiler.NativeRow
import Airbender.Import.Compiler.Rows.MulDivUncached

namespace Airbender.Compiler.PooledRowNative.MulDivUncached
open Airbender Airbender.Compiler

/-- Nonzero physical generic/range16 requests belong to their independently
interpreted setup columns. This predicate is a consequence of LookupArguments. -/
def PhysicalAuthoredLookupValid (physical : GKRAddress → Source.BaseField) : Prop :=
  (∀ query ∈ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.Contains Airbender.Compiler.TableNative.MulDivUncached.native.genericSetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement))))
  ∧ (∀ query ∈ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.Contains Airbender.Compiler.TableNative.MulDivUncached.native.range16SetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement))))

/-- Source-projected logical operands at the physical source, borrow and
history coordinates. The public lookup argument matches nativeRequests; the
supporting proof transports that matching to this source interpretation. -/
noncomputable def physicalRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)),
    Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivUncached.native.sourcePlacement)),
    Airbender.Compiler.HelperNative.MulDivUncached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.HelperNative.MulDivUncached.native.placement.project
        (input.physical ∘ Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address))] 1)]).get group

/-- Expanded native lookup operands before alpha compression. The encodings and
masks are independently imported from the consumed native leaves; timestamp
recipes retain the physical borrow and memory-history coordinates. -/
noncomputable def nativeOperands (input : Input) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  ([[(18, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf18.weight.value input.physical)),
      (19, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding19.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf19.weight.value input.physical)),
      (20, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding20.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf20.weight.value input.physical)),
      (21, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding21.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf21.weight.value input.physical)),
      (22, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding22.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf22.weight.value input.physical)),
      (23, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding23.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf23.weight.value input.physical)),
      (26, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding26.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf26.weight.value input.physical)),
      (27, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding27.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf27.weight.value input.physical)),
      (16, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf16.weight.value input.physical))],
      [(0, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf0.weight.value input.physical)),
      (2, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf2.weight.value input.physical)),
      (3, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf3.weight.value input.physical)),
      (4, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf4.weight.value input.physical)),
      (5, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf5.weight.value input.physical)),
      (6, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf6.weight.value input.physical)),
      (7, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf7.weight.value input.physical)),
      (24, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding24.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf24.weight.value input.physical))],
      [(8, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf8.weight.value input.physical)),
      (10, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf10.weight.value input.physical)),
      (11, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf11.weight.value input.physical)),
      (12, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf12.weight.value input.physical)),
      (13, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf13.weight.value input.physical)),
      (14, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf14.weight.value input.physical)),
      (15, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf15.weight.value input.physical)),
      (25, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.encoding25.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.leaf25.weight.value input.physical))]]).get group

def nativeSetupLeaf (group : Fin 3) : Nat :=
  ([17,
      1,
      9]).get group

noncomputable def nativeRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  (nativeOperands input group).map Prod.snd
-- End expanded native lookup operands.

/-- Exact matching of every enabled emitted tuple against the corresponding
literal setup columns. The generic Review definition states exact matching;
this generated binding selects the three setup-column groups and native tuples. -/
def LookupArguments (input : Input) : Type :=
  GroupedLookupArguments
    (fun group : Fin 3 => Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.fields
      (([Airbender.Compiler.TableNative.MulDivUncached.native.genericSetupColumns,
         Airbender.Compiler.TableNative.MulDivUncached.native.range16SetupColumns,
         Airbender.Compiler.TableNative.MulDivUncached.native.timestampSetupColumns]).get group))
    (fun group => activeLookupFields (nativeRequests input group))

/-- Match the same native tuples against independently supplied setup rows.
The calling boundary must bind these rows to public text and fixed setup data. -/
def LookupArgumentsWith
    (tables : Fin 3 → Fin Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.imported.data.length →
      List Source.BaseField) (input : Input) : Type :=
  GroupedLookupArguments tables (fun group => activeLookupFields (nativeRequests input group))

/-- The retained setup gives exactly the existing lookup argument type. -/
theorem lookup_arguments_with_retained (input : Input) :
    LookupArgumentsWith
      (fun group : Fin 3 => Airbender.Compiler.MaterializedNative.MulDivUncached.native.model.fields
        (([Airbender.Compiler.TableNative.MulDivUncached.native.genericSetupColumns,
           Airbender.Compiler.TableNative.MulDivUncached.native.range16SetupColumns,
           Airbender.Compiler.TableNative.MulDivUncached.native.timestampSetupColumns]).get group)) input =
      LookupArguments input := rfl
-- End generated logical lookup argument.

def inputRow (input : Input) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.mulDiv, (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.address
    (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.placement index)) input.physical)⟩

end Airbender.Compiler.PooledRowNative.MulDivUncached
