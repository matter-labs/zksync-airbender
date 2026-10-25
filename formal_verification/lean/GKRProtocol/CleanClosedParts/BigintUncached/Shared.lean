import GKRProtocol.CleanArgumentsNative.BigintUncached
import GKRProtocol.CleanScalarNative.BigintUncached
import GKRProtocol.CleanPrimitiveLookups
import GKRProtocol.CleanLinksNative.BigintUncached
import GKRProtocol.MaterializedWitnessNative.BigintUncached
import GKRProtocol.CleanGenericArgumentsNative.BigintUncached
import GKRProtocol.CleanGenericSetup

namespace Airbender.Compiler.CleanClosedNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 3) :=
  Airbender.Compiler.MaterializedNative.BigintUncached.native.model.imported.data.table "Airbender.Native.Bigint"

theorem generic_columns_inventory : Airbender.Compiler.TableNative.BigintUncached.native.genericSetupColumns =
    (List.range 3).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.Bigint.clockConstraints (p := babyBearModulus) nativeSetup) =
    (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpressions.map Verification.range16) ++
    ((Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpressions.drop 39).map Trace.timestampLookup) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpressions.map Trace.timestampLookup) := by rfl


end Airbender.Compiler.CleanClosedNative.BigintUncached
