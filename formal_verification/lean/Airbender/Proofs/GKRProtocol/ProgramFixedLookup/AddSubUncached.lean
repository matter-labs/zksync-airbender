import Airbender.Proofs.GKRProtocol.ProgramNativeTransport.AddSubUncached
import Airbender.Proofs.GKRProtocol.ProgramSetupNative
import Airbender.Proofs.GKRProtocol.NativeProgramQueries

namespace Airbender.Compiler.ProgramFixedLookup.AddSubUncached
open Airbender Airbender.Compiler Airbender.Compiler.PooledRowNative.AddSubUncached
set_option warningAsError true
set_option Elab.async false

/-- Range and timestamp matching use the unchanged native setup groups. -/
theorem fixed_group_member
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubUncached group index.val) input)
    (group : Fin 3) (other : group.val ≠ 0) (query : MaterializedQuery)
    (member : query ∈ physicalRequests input group) (enabled : query.weight ≠ 0) :
    Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains (Airbender.Compiler.MaterializedWitnessNative.AddSubUncached.setupColumns group) query.fields := by
  obtain ⟨index, equal⟩ := source_member_with (fun group index => NativeProgramSetup.rows decoder wordAt .addSubUncached group index.val)
    input arguments group query member enabled
  rw [NativeProgramSetup.rows_fixed_group decoder wordAt .addSubUncached group index.val other] at equal
  refine ⟨index, ?_⟩
  simpa only [NativeProgramSetup.retainedRows, dif_pos index.isLt, Airbender.Compiler.MaterializedWitnessNative.AddSubUncached.setupColumns] using equal

theorem range_from_arguments
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubUncached group index.val) input) :
    ∀ query ∈ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries,
      query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement) ≠ 0 →
        Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains Airbender.Compiler.TableNative.AddSubUncached.native.range16SetupColumns
          (query.fields.map (fun field => field.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement))) := by
  intro query member enabled
  apply fixed_group_member decoder wordAt input arguments 1 (by decide +kernel)
    (query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.AddSubUncached.native.sourcePlacement)) ?_ enabled
  exact List.mem_map.mpr ⟨query, member, rfl⟩

theorem helpers_from_arguments (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .addSubUncached group index.val) input) :
    ∀ field ∈ Airbender.Compiler.HelperNative.AddSubUncached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.AddSubUncached.native.sourceValues input.physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.AddSubUncached.native.sourceValues input.physical)
  have present := fixed_group_member decoder wordAt input arguments 2 (by decide +kernel) (MaterializedQuery.mk [value] 1)
    (by simpa [physicalRequests, value, Airbender.Compiler.HelperNative.AddSubUncached.native.sourceValues] using
          (List.mem_map.mpr ⟨field, member, rfl⟩ :
            MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.AddSubUncached.native.sourceValues input.physical)] 1 ∈
              Airbender.Compiler.HelperNative.AddSubUncached.native.fields.map (fun item => MaterializedQuery.mk
                [item.value (Airbender.Compiler.HelperNative.AddSubUncached.native.sourceValues input.physical)] 1))) one_ne_zero
  change Airbender.Compiler.MaterializedNative.AddSubUncached.native.model.Contains [.timestamp] [value] at present
  exact Airbender.Compiler.MaterializedRangeNative.AddSubUncached.native.timestamp_bounded value present

end Airbender.Compiler.ProgramFixedLookup.AddSubUncached
