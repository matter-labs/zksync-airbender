import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.BigintCached
import Airbender.Proofs.GKRProtocol.CleanScalarNative.BigintCached
import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups
import Airbender.Proofs.GKRProtocol.CleanLinksNative.BigintCached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.BigintCached
import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsNative.BigintCached
import Airbender.Proofs.GKRProtocol.CleanGenericSetup

namespace Airbender.Compiler.CleanClosedNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 3) :=
  Airbender.Compiler.MaterializedNative.BigintCached.native.model.imported.data.table "Airbender.Native.Bigint"

theorem generic_columns_inventory : Airbender.Compiler.TableNative.BigintCached.native.genericSetupColumns =
    (List.range 3).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.Bigint.clockConstraints (p := babyBearModulus) nativeSetup) =
    (Airbender.Compiler.CleanArgumentsNative.BigintCached.native.rangeExpressions.map Verification.range16) ++
    ((Airbender.Compiler.CleanArgumentsNative.BigintCached.native.timestampExpressions.drop 39).map Trace.timestampLookup) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.BigintCached.native.timestampExpressions.map Trace.timestampLookup) := by rfl


end Airbender.Compiler.CleanClosedNative.BigintCached
