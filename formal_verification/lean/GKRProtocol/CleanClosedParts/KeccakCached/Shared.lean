import GKRProtocol.CleanArgumentsNative.KeccakCached
import GKRProtocol.CleanScalarNative.KeccakCached
import GKRProtocol.CleanPrimitiveLookups
import GKRProtocol.CleanLinksNative.KeccakCached
import GKRProtocol.MaterializedWitnessNative.KeccakCached
import GKRProtocol.CleanGenericArgumentsNative.KeccakCached
import GKRProtocol.CleanGenericSetup

namespace Airbender.Compiler.CleanClosedNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 8) :=
  Airbender.Compiler.MaterializedNative.KeccakCached.native.model.imported.data.table "Airbender.Native.Keccak"

theorem generic_columns_inventory : Airbender.Compiler.TableNative.KeccakCached.native.genericSetupColumns =
    (List.range 8).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.Keccak.clockConstraints (p := babyBearModulus) nativeSetup) =
    (Airbender.Compiler.CleanArgumentsNative.KeccakCached.native.rangeExpressions.map Verification.range16) ++
    ((Airbender.Compiler.CleanArgumentsNative.KeccakCached.native.timestampExpressions.drop 29).map Trace.timestampLookup) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.KeccakCached.native.timestampExpressions.map Trace.timestampLookup) := by rfl


end Airbender.Compiler.CleanClosedNative.KeccakCached
