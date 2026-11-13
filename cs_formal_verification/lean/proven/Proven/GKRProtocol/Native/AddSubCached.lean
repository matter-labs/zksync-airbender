module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.LookupImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.LookupNative.AddSubCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_lookup_fields native from "artifacts/compiler/add-sub-cached.json"
  source "artifacts/compiler/add-sub-cached-source.json"
  certificate "artifacts/compiler/lookup/add-sub-cached.json"

theorem request_fields_preserved {values} (holds : Satisfies native.copyRelations values) :
    ∀ field ∈ native.fields,
      field.source.value (values ∘ native.sourcePlacement) = field.lowered.value values := by
  intro field member
  exact LookupFieldAgreement.sound native.sourcePlacement
    (List.all_eq_true.mp native.checked field member) holds

end Airbender.Compiler.LookupNative.AddSubCached
