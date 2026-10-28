import Airbender.Review.Compiler.LookupArgument
import Airbender.Review.Compiler.NativeRow
import Airbender.Import.Compiler.Rows.JumpBranchCached

namespace Airbender.Compiler.PooledRowNative.JumpBranchCached
open Airbender Airbender.Compiler

/-- Nonzero physical generic/range16 requests belong to their independently
interpreted setup columns. This predicate is a consequence of LookupArguments. -/
def PhysicalAuthoredLookupValid (physical : GKRAddress → Source.BaseField) : Prop :=
  (∀ query ∈ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.Contains Airbender.Compiler.TableNative.JumpBranchCached.native.genericSetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement))))
  ∧ (∀ query ∈ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries,
    query.weight (RingHom.id _) ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement) ≠ 0 →
    Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.Contains Airbender.Compiler.TableNative.JumpBranchCached.native.range16SetupColumns
      (query.fields.map (fun field => field.value ((physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement))))

/-- Source-projected logical operands at the physical source, borrow and
history coordinates. The public lookup argument matches nativeRequests; the
supporting proof transports that matching to this source interpretation. -/
noncomputable def physicalRequests (input : Input) (group : Fin 3) : List MaterializedQuery :=
  ([Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)),
    Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries.map (fun query => query.materialized
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.JumpBranchCached.native.sourcePlacement)),
    Airbender.Compiler.HelperNative.JumpBranchCached.native.fields.map (fun field => MaterializedQuery.mk
      [field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.placement.project
        (input.physical ∘ Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.address))] 1)]).get group

/-- Expanded native lookup operands before alpha compression. The encodings and
masks are independently imported from the consumed native leaves; timestamp
recipes retain the physical borrow and memory-history coordinates. -/
noncomputable def nativeOperands (input : Input) (group : Fin 3) : List (Nat × MaterializedQuery) :=
  ([[(14, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding14.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf14.weight.value input.physical)),
      (15, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding15.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf15.weight.value input.physical)),
      (16, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding16.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf16.weight.value input.physical)),
      (17, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding17.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf17.weight.value input.physical)),
      (12, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding12.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf12.weight.value input.physical))],
      [(0, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding0.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf0.weight.value input.physical)),
      (2, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding2.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf2.weight.value input.physical)),
      (3, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding3.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf3.weight.value input.physical)),
      (18, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding18.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf18.weight.value input.physical))],
      [(4, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding4.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf4.weight.value input.physical)),
      (6, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding6.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf6.weight.value input.physical)),
      (7, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding7.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf7.weight.value input.physical)),
      (8, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding8.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf8.weight.value input.physical)),
      (9, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding9.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf9.weight.value input.physical)),
      (10, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding10.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf10.weight.value input.physical)),
      (11, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding11.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf11.weight.value input.physical)),
      (19, MaterializedQuery.mk (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.encoding19.fields input.physical)
        (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.leaf19.weight.value input.physical))]]).get group

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
    (fun group : Fin 3 => Airbender.Compiler.MaterializedNative.JumpBranchCached.native.model.fields
      (([Airbender.Compiler.TableNative.JumpBranchCached.native.genericSetupColumns,
         Airbender.Compiler.TableNative.JumpBranchCached.native.range16SetupColumns,
         Airbender.Compiler.TableNative.JumpBranchCached.native.timestampSetupColumns]).get group))
    (fun group => activeLookupFields (nativeRequests input group))
-- End generated logical lookup argument.

def inputRow (input : Input) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.jumpBranchSlt, (physicalAssignment (fun index => Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address
    (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.placement index)) input.physical)⟩

end Airbender.Compiler.PooledRowNative.JumpBranchCached
