import Airbender.Review.Compiler.LookupArgument
import Airbender.Review.Compiler.NativeRow
import Airbender.Import.Compiler.Rows.UnifiedUncached

namespace Airbender.Compiler.UnifiedRowNative.UnifiedUncached
open Airbender Airbender.Compiler

/-- Nonzero physical generic/range16 requests belong to their independently
interpreted setup columns. This predicate is a consequence of LookupArguments. -/
def PhysicalAuthoredLookupValid (physical : GKRAddress → Source.BaseField) : Prop :=
  (∀ query ∈ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement))))
  ∧ (∀ query ∈ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains Airbender.Compiler.TableNative.UnifiedUncached.native.range16SetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement))))

/-- Source-projected logical operands at the physical source, borrow and
history coordinates. The public lookup argument matches nativeRequests; the
supporting proof transports that matching to this source interpretation. -/
noncomputable def physicalRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)),
    Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)),
    Airbender.Compiler.HelperNative.UnifiedUncached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.HelperNative.UnifiedUncached.native.placement.project
        (input.physical ∘ Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank.address))] 1)]).get group

/-- Expanded native lookup operands before alpha compression. The encodings and
masks are independently imported from the consumed native leaves; timestamp
recipes retain the physical borrow and memory-history coordinates. -/
noncomputable def nativeOperands (input : Input) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  ([[(25, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding25.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf25.weight.value input.physical)),
      (26, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding26.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf26.weight.value input.physical)),
      (27, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding27.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf27.weight.value input.physical)),
      (28, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding28.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf28.weight.value input.physical)),
      (29, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding29.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf29.weight.value input.physical)),
      (20, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding20.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf20.weight.value input.physical))],
      [(0, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf0.weight.value input.physical)),
      (2, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf2.weight.value input.physical)),
      (3, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf3.weight.value input.physical)),
      (4, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf4.weight.value input.physical)),
      (5, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf5.weight.value input.physical)),
      (6, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf6.weight.value input.physical)),
      (7, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf7.weight.value input.physical)),
      (8, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf8.weight.value input.physical)),
      (9, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf9.weight.value input.physical)),
      (10, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf10.weight.value input.physical)),
      (23, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding23.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf23.weight.value input.physical)),
      (11, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf11.weight.value input.physical)),
      (22, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding22.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf22.weight.value input.physical))],
      [(12, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf12.weight.value input.physical)),
      (14, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf14.weight.value input.physical)),
      (15, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf15.weight.value input.physical)),
      (16, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf16.weight.value input.physical)),
      (17, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf17.weight.value input.physical)),
      (18, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf18.weight.value input.physical)),
      (19, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding19.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf19.weight.value input.physical)),
      (24, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.encoding24.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.leaf24.weight.value input.physical))]]).get group

def nativeSetupLeaf (group : Fin 3) : Nat :=
  ([21,
      1,
      13]).get group

noncomputable def nativeRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  (nativeOperands input group).map Prod.snd
-- End expanded native lookup operands.

/-- Exact matching of every enabled emitted tuple against the corresponding
literal setup columns. This is the retained logical argument boundary; sampled
field-sum equality is insufficient. Source membership and helper ranges are
consequences, not fields of this contract. -/
def LookupArguments (input : Input) : Type :=
  (group : Fin 3) → LookupArgument
    (Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.fields (([Airbender.Compiler.TableNative.UnifiedUncached.native.genericSetupColumns, Airbender.Compiler.TableNative.UnifiedUncached.native.range16SetupColumns, Airbender.Compiler.TableNative.UnifiedUncached.native.timestampSetupColumns]).get group))
    (activeLookupFields (nativeRequests input group))

def inputRow (input : Input) : Trace.Row babyBearModulus Trace.UnifiedFamily :=
  ⟨.machine, (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.bank.address
    (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.placement index)) input.physical)⟩

end Airbender.Compiler.UnifiedRowNative.UnifiedUncached
