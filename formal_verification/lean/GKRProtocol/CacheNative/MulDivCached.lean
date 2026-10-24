import GKRProtocol.CacheImport
import GKRCompiler.WiringNative.MulDivCached

namespace Airbender.Compiler.CacheNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_cache_bindings native from "artifacts/compiler/mul-div-cached.json"
  wiring Airbender.Compiler.WiringNative.MulDivCached.native

theorem cache_ports_checked {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) :
    (native.bindings hom challenges).all CacheBinding.portsValid = true :=
  native.portsChecked hom challenges

theorem cache_claims_bound {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (point : List R) (rows : List Bool → GKRAddress → R) :
    ∀ binding ∈ native.bindings hom challenges,
      multilinearEvaluation point (binding.materialize rows) = binding.expectedClaim point rows :=
  fun binding _ => binding.claim_bound point rows

end Airbender.Compiler.CacheNative.MulDivCached
