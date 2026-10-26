import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.CleanScalarNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups
import Airbender.Proofs.GKRProtocol.CleanLinksNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.CleanGenericSetup

namespace Airbender.Compiler.CleanClosedNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 8) :=
  Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.imported.data.table "Airbender.Native.Keccak"

theorem generic_columns_inventory : Airbender.Compiler.TableNative.KeccakUncached.native.genericSetupColumns =
    (List.range 8).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.Keccak.clockConstraints (p := babyBearModulus) nativeSetup) =
    (Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.rangeExpressions.map Verification.range16) ++
    ((Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpressions.drop 29).map Trace.timestampLookup) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpressions.map Trace.timestampLookup) := by rfl


end Airbender.Compiler.CleanClosedNative.KeccakUncached
