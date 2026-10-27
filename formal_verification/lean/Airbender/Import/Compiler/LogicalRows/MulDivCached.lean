import Airbender.Review.Compiler.LookupArgument
import Airbender.Review.Compiler.NativeRow
import Airbender.Import.Compiler.Rows.MulDivCached

namespace Airbender.Compiler.PooledRowNative.MulDivCached
open Airbender Airbender.Compiler

/-- Nonzero physical generic/range16 requests belong to their independently
interpreted setup columns. This predicate is a consequence of LookupArguments. -/
def PhysicalAuthoredLookupValid (physical : GKRAddress → Source.BaseField) : Prop :=
  (∀ query ∈ Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.MulDivCached.native.model.Contains Airbender.Compiler.TableNative.MulDivCached.native.genericSetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement))))
  ∧ (∀ query ∈ Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.MulDivCached.native.model.Contains Airbender.Compiler.TableNative.MulDivCached.native.range16SetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement))))

/-- Source-projected logical operands at the physical source, borrow and
history coordinates. The public lookup argument matches nativeRequests; the
supporting proof transports that matching to this source interpretation. -/
noncomputable def physicalRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)),
    Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement)),
    Airbender.Compiler.HelperNative.MulDivCached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.HelperNative.MulDivCached.native.placement.project
        (input.physical ∘ Airbender.Compiler.MemoryNative.MulDivCached.native.bank.address))] 1)]).get group

/-- Expanded native lookup operands before alpha compression. The encodings and
masks are independently imported from the consumed native leaves; timestamp
recipes retain the physical borrow and memory-history coordinates. -/
noncomputable def nativeOperands (input : Input) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  ([[(18, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf18.weight.value input.physical)),
      (19, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding19.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf19.weight.value input.physical)),
      (20, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding20.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf20.weight.value input.physical)),
      (21, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding21.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf21.weight.value input.physical)),
      (22, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding22.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf22.weight.value input.physical)),
      (23, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding23.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf23.weight.value input.physical)),
      (26, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding26.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf26.weight.value input.physical)),
      (27, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding27.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf27.weight.value input.physical)),
      (16, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf16.weight.value input.physical))],
      [(0, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf0.weight.value input.physical)),
      (2, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf2.weight.value input.physical)),
      (3, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf3.weight.value input.physical)),
      (4, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf4.weight.value input.physical)),
      (5, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf5.weight.value input.physical)),
      (6, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf6.weight.value input.physical)),
      (7, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf7.weight.value input.physical)),
      (24, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding24.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf24.weight.value input.physical))],
      [(8, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf8.weight.value input.physical)),
      (10, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf10.weight.value input.physical)),
      (11, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf11.weight.value input.physical)),
      (12, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf12.weight.value input.physical)),
      (13, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf13.weight.value input.physical)),
      (14, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf14.weight.value input.physical)),
      (15, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf15.weight.value input.physical)),
      (25, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding25.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf25.weight.value input.physical))]]).get group

def nativeSetupLeaf (group : Fin 3) : Nat :=
  ([17,
      1,
      9]).get group

noncomputable def nativeRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  (nativeOperands input group).map Prod.snd
-- End expanded native lookup operands.

/-- Exact matching of every enabled emitted tuple against the corresponding
literal setup columns. This is the retained logical argument boundary; sampled
field-sum equality is insufficient. Source membership and helper ranges are
consequences, not fields of this contract. -/
def LookupArguments (input : Input) : Type :=
  (group : Fin 3) → LookupArgument
    (Airbender.Compiler.MaterializedNative.MulDivCached.native.model.fields (([Airbender.Compiler.TableNative.MulDivCached.native.genericSetupColumns, Airbender.Compiler.TableNative.MulDivCached.native.range16SetupColumns, Airbender.Compiler.TableNative.MulDivCached.native.timestampSetupColumns]).get group))
    (activeLookupFields (nativeRequests input group))

def inputRow (input : Input) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.mulDiv, (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address
    (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.placement index)) input.physical)⟩

end Airbender.Compiler.PooledRowNative.MulDivCached
