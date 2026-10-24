import GKRProtocol.BaseEncoding
import GKRProtocol.CacheNative.AddSubCached
import GKRProtocol.ConsumerNative.AddSubCached

namespace Tests.GKRBaseEncoding
open Airbender Airbender.Compiler
set_option warningAsError true
set_option maxRecDepth 32768

private noncomputable def vectorCache := CacheNative.AddSubCached.native.rawCache14
private noncomputable def scalarCache := CacheNative.AddSubCached.native.rawCache8
private noncomputable def typing := ConsumerNative.AddSubCached.native.typing
private noncomputable def definition : AffineDefinition := ⟨vectorCache.output, vectorCache.program⟩

/-- A materialized vector lives in the extension field. Its address cannot be
used as an unconstrained base-field source column. -/
theorem rejects_vector_cache_as_base_column :
    (NativeLookupEncoding.scalar (.input vectorCache.output)).baseCheck typing = false := by decide +kernel

theorem accepts_scalar_cache_base_role :
    (NativeLookupEncoding.scalar (.input scalarCache.output)).baseCheck typing = true := by decide +kernel

theorem expands_actual_cache_definition :
    LookupPayload.expand [definition] [0] (.input vectorCache.output) = some vectorCache.program := by rfl

theorem rejects_unknown_definition_selector :
    (LookupPayload.expand [definition] [1] (.input vectorCache.output)).isSome = false := by decide +kernel

theorem rejects_replacement_payload :
    LookupPayload.expand [definition] [0] (.input vectorCache.output) ≠
      some (.constant (.natural 0)) := by
  intro replaced
  have wrong := congrArg (fun payload : Option LookupPayload =>
    payload.map (fun program => program.inputs.length)) replaced
  cases wrong

end Tests.GKRBaseEncoding
