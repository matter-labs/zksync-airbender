import GKRProtocol.CleanArgumentsNative.BlakeGUncached
import GKRProtocol.CleanScalarNative.BlakeGUncached
import GKRProtocol.CleanPrimitiveLookups
import GKRProtocol.CleanLinksNative.BlakeGUncached
import GKRProtocol.MaterializedWitnessNative.BlakeGUncached
import GKRProtocol.CleanGenericArgumentsNative.BlakeGUncached
import GKRProtocol.CleanGenericSetup

namespace Airbender.Compiler.CleanClosedNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 9) :=
  Airbender.Compiler.MaterializedNative.BlakeGUncached.native.model.imported.data.table "Airbender.Native.Blake2G"

theorem generic_columns_inventory : Airbender.Compiler.TableNative.BlakeGUncached.native.genericSetupColumns =
    (List.range 9).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.Blake2G.clockConstraints (p := babyBearModulus) nativeSetup) =
    (Airbender.Compiler.CleanArgumentsNative.BlakeGUncached.native.rangeExpressions.map Verification.range16) ++
    ((Airbender.Compiler.CleanArgumentsNative.BlakeGUncached.native.timestampExpressions.drop 19).map Trace.timestampLookup) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.BlakeGUncached.native.timestampExpressions.map Trace.timestampLookup) := by rfl


end Airbender.Compiler.CleanClosedNative.BlakeGUncached
