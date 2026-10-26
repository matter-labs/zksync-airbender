import Airbender.Import.GKRProtocol.LookupImport

namespace Airbender.Compiler.LookupNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_lookup_fields native from "artifacts/compiler/unified-uncached.json"
  source "artifacts/compiler/unified-uncached-source.json"
  certificate "artifacts/compiler/lookup/unified-uncached.json"

theorem request_fields_preserved {values} (holds : Satisfies native.copyRelations values) :
    ∀ field ∈ native.fields,
      field.source.value (values ∘ native.sourcePlacement) = field.lowered.value values := by
  intro field member
  exact LookupFieldAgreement.sound native.sourcePlacement
    (List.all_eq_true.mp native.checked field member) holds

end Airbender.Compiler.LookupNative.UnifiedUncached
