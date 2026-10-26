import Airbender.Proofs.GKRProtocol.CleanArgumentsNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.CleanScalarNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups
import Airbender.Proofs.GKRProtocol.CleanLinksNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.CleanGenericSetup

namespace Airbender.Compiler.CleanClosedNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def nativeSetup : Table Source.BaseField (fields 6) :=
  Airbender.Compiler.MaterializedNative.BlakeRoundUncached.native.model.imported.data.table "Airbender.Native.Blake2Round"

theorem generic_columns_inventory : Airbender.Compiler.TableNative.BlakeRoundUncached.native.genericSetupColumns =
    (List.range 6).map SourceSetupColumn.generic := by decide +kernel

theorem clock_lookup_inventory :
    FlatOperation.lookups (Airbender.Blake2Round.clockConstraints (p := babyBearModulus) nativeSetup) =
    (Airbender.Compiler.CleanArgumentsNative.BlakeRoundUncached.native.rangeExpressions.map Verification.range16) ++
    ((Airbender.Compiler.CleanArgumentsNative.BlakeRoundUncached.native.timestampExpressions.drop 87).map Trace.timestampLookup) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.BlakeRoundUncached.native.timestampExpressions.map Trace.timestampLookup) := by rfl


end Airbender.Compiler.CleanClosedNative.BlakeRoundUncached
