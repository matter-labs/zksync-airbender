import GKRProtocol.CleanArgumentsNative.BlakeGCached
import GKRProtocol.CleanScalarNative.BlakeGCached
import GKRProtocol.CleanPrimitiveLookups
import GKRProtocol.CleanLinksNative.BlakeGCached
import GKRProtocol.MaterializedWitnessNative.BlakeGCached
import GKRProtocol.CleanGenericArgumentsNative.BlakeGCached
import GKRProtocol.CleanGenericSetup

namespace Airbender.Compiler.CleanClosedNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 9) :=
  Airbender.Compiler.MaterializedNative.BlakeGCached.native.model.imported.data.table "Airbender.Native.Blake2G"

theorem generic_columns_inventory : Airbender.Compiler.TableNative.BlakeGCached.native.genericSetupColumns =
    (List.range 9).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.Blake2G.clockConstraints (p := babyBearModulus) nativeSetup) =
    (Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.rangeExpressions.map Verification.range16) ++
    ((Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpressions.drop 19).map Trace.timestampLookup) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpressions.map Trace.timestampLookup) := by rfl


end Airbender.Compiler.CleanClosedNative.BlakeGCached
