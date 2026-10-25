import GKRProtocol.CleanArgumentsNative.BlakeRoundCached
import GKRProtocol.CleanScalarNative.BlakeRoundCached
import GKRProtocol.CleanPrimitiveLookups
import GKRProtocol.CleanLinksNative.BlakeRoundCached
import GKRProtocol.MaterializedWitnessNative.BlakeRoundCached
import GKRProtocol.CleanGenericArgumentsNative.BlakeRoundCached
import GKRProtocol.CleanGenericSetup

namespace Airbender.Compiler.CleanClosedNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 6) :=
  Airbender.Compiler.MaterializedNative.BlakeRoundCached.native.model.imported.data.table "Airbender.Native.Blake2Round"

theorem generic_columns_inventory : Airbender.Compiler.TableNative.BlakeRoundCached.native.genericSetupColumns =
    (List.range 6).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.Blake2Round.clockConstraints (p := babyBearModulus) nativeSetup) =
    (Airbender.Compiler.CleanArgumentsNative.BlakeRoundCached.native.rangeExpressions.map Verification.range16) ++
    ((Airbender.Compiler.CleanArgumentsNative.BlakeRoundCached.native.timestampExpressions.drop 87).map Trace.timestampLookup) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.BlakeRoundCached.native.timestampExpressions.map Trace.timestampLookup) := by rfl


end Airbender.Compiler.CleanClosedNative.BlakeRoundCached
