import Airbender.Review.Compiler.LookupArgument
import Airbender.Review.Compiler.NativeRow
import Airbender.Import.Compiler.Rows.ShiftBinopCached

namespace Airbender.Compiler.PooledRowNative.ShiftBinopCached
open Airbender Airbender.Compiler

/-- Nonzero physical generic/range16 requests belong to their independently
interpreted setup columns. This predicate is a consequence of LookupArguments. -/
def PhysicalAuthoredLookupValid (physical : GKRAddress → Source.BaseField) : Prop :=
  (∀ query ∈ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopCached.native.genericSetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement))))
  ∧ (∀ query ∈ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopCached.native.range16SetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement))))

/-- Source-projected logical operands at the physical source, borrow and
history coordinates. The public lookup argument matches nativeRequests; the
supporting proof transports that matching to this source interpretation. -/
noncomputable def physicalRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)),
    Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)),
    Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.placement.project
        (input.physical ∘ Airbender.Compiler.MemoryNative.ShiftBinopCached.native.bank.address))] 1)]).get group

/-- Expanded native lookup operands before alpha compression. The encodings and
masks are independently imported from the consumed native leaves; timestamp
recipes retain the physical borrow and memory-history coordinates. -/
noncomputable def nativeOperands (input : Input) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  ([[(14, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf14.weight.value input.physical)),
      (15, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf15.weight.value input.physical)),
      (16, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf16.weight.value input.physical)),
      (17, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf17.weight.value input.physical)),
      (18, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf18.weight.value input.physical)),
      (10, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf10.weight.value input.physical))],
      [(0, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf0.weight.value input.physical)),
      (12, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf12.weight.value input.physical))],
      [(2, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf2.weight.value input.physical)),
      (4, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf4.weight.value input.physical)),
      (5, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding5.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf5.weight.value input.physical)),
      (6, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf6.weight.value input.physical)),
      (7, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf7.weight.value input.physical)),
      (8, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf8.weight.value input.physical)),
      (9, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf9.weight.value input.physical)),
      (13, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.encoding13.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.leaf13.weight.value input.physical))]]).get group

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
    (fun group : Fin 3 => Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.fields
      (([Airbender.Compiler.TableNative.ShiftBinopCached.native.genericSetupColumns,
         Airbender.Compiler.TableNative.ShiftBinopCached.native.range16SetupColumns,
         Airbender.Compiler.TableNative.ShiftBinopCached.native.timestampSetupColumns]).get group))
    (fun group => activeLookupFields (nativeRequests input group))
-- End generated logical lookup argument.

def inputRow (input : Input) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.shiftBinop, (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address
    (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.placement index)) input.physical)⟩

end Airbender.Compiler.PooledRowNative.ShiftBinopCached
