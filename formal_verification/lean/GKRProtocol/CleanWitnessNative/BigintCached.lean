import GKRProtocol.CleanClosedNative.BigintCached
import GKRProtocol.FramedWitnessNative.BigintCached

namespace Airbender.Compiler.CleanWitnessNative.BigintCached
open Airbender Airbender.Compiler
open Airbender.Compiler.MaterializedWitnessNative.BigintCached Airbender.Compiler.FramedWitnessNative.BigintCached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem complete_trace_clean_extends
    (sourceValue : Fin Airbender.Compiler.MaterializedNative.BigintCached.native.model.imported.data.length → Fin 277 → Source.BaseField)
    (original : ∀ row, Satisfies (Airbender.Compiler.SourceContractNative.BigintCached.native.originals.map Expression.polynomial) (sourceValue row))
    (clockValid : ∀ row, Source.clockContract Airbender.Compiler.SourceContractNative.BigintCached.native.clock (Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement.memory.project (sourceValue row)))
    (primitives : ∀ row, Airbender.Compiler.HelperValidityNative.BigintCached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.BigintCached.native.execute.value (Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement.memory.project (sourceValue row)))
      (Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement.memory.project (sourceValue row)))
    (authored : ∀ row, AuthoredLookupValid (sourceValue row))
    (fallback : Fin Airbender.Compiler.MaterializedNative.BigintCached.native.model.imported.data.length → GKRAddress → Source.BaseField)
    (data : Fin Airbender.Compiler.MaterializedNative.BigintCached.native.model.imported.data.length → ProverData Source.BaseField) :
    ∃ counts : Fin Airbender.Compiler.MaterializedNative.BigintCached.native.model.imported.data.length → Fin 3 → Source.BaseField,
      ∀ {R : Type} [CommRing R] (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R),
      ∃ baseValue : Fin Airbender.Compiler.MaterializedNative.BigintCached.native.model.imported.data.length → GKRAddress → Source.BaseField,
      ∃ values : Fin Airbender.Compiler.MaterializedNative.BigintCached.native.model.imported.data.length → GKRAddress → R,
        (∀ row, CompleteRowWitness hom challenges gamma (sourceValue row) (counts row) row (fallback row) (baseValue row) (values row)) ∧
        (∀ group : Fin 3, ((List.finRange Airbender.Compiler.MaterializedNative.BigintCached.native.model.imported.data.length).map
          (fun row => (outputPorts group).value (values row))).sum.numerator = 0) ∧
        ∀ row, FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment (baseValue row) (data row)) (Airbender.Bigint.clockConstraints (p := babyBearModulus) Airbender.Compiler.CleanClosedNative.BigintCached.nativeSetup) := by
  obtain ⟨counts, constructed⟩ := Airbender.Compiler.FramedWitnessNative.BigintCached.complete_trace_extends sourceValue original clockValid primitives authored fallback
  refine ⟨counts, ?_⟩
  intro R _ hom challenges gamma
  obtain ⟨baseValue, values, correct, cancel⟩ := constructed hom challenges gamma
  refine ⟨baseValue, values, correct, cancel, ?_⟩
  intro row
  have witness := (correct row).1
  rcases witness with ⟨inputsAt, arithmetic, _, _, _, _, _, _, helpers, _⟩
  exact Airbender.Compiler.CleanClosedNative.BigintCached.retained_clock_from_source (sourceValue row) (counts row) (baseValue row) (data row)
    inputsAt arithmetic helpers (authored row)

end Airbender.Compiler.CleanWitnessNative.BigintCached
