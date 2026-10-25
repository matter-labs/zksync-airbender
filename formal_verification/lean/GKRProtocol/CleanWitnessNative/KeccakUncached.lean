import GKRProtocol.CleanClosedNative.KeccakUncached
import GKRProtocol.FramedWitnessNative.KeccakUncached

namespace Airbender.Compiler.CleanWitnessNative.KeccakUncached
open Airbender Airbender.Compiler
open Airbender.Compiler.MaterializedWitnessNative.KeccakUncached Airbender.Compiler.FramedWitnessNative.KeccakUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem complete_trace_clean_extends
    (sourceValue : Fin Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.imported.data.length → Fin 267 → Source.BaseField)
    (original : ∀ row, Satisfies (Airbender.Compiler.SourceContractNative.KeccakUncached.native.originals.map Expression.polynomial) (sourceValue row))
    (clockValid : ∀ row, Source.clockContract Airbender.Compiler.SourceContractNative.KeccakUncached.native.clock (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.helperPlacement.memory.project (sourceValue row)))
    (primitives : ∀ row, Airbender.Compiler.HelperValidityNative.KeccakUncached.native.profile.ExecutionValid (Airbender.Compiler.HelperValidityNative.KeccakUncached.native.execute.value (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.helperPlacement.memory.project (sourceValue row)))
      (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.helperPlacement.memory.project (sourceValue row)))
    (authored : ∀ row, AuthoredLookupValid (sourceValue row))
    (fallback : Fin Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.imported.data.length → GKRAddress → Source.BaseField)
    (data : Fin Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.imported.data.length → ProverData Source.BaseField) :
    ∃ counts : Fin Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.imported.data.length → Fin 2 → Source.BaseField,
      ∀ {R : Type} [CommRing R] (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R),
      ∃ baseValue : Fin Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.imported.data.length → GKRAddress → Source.BaseField,
      ∃ values : Fin Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.imported.data.length → GKRAddress → R,
        (∀ row, CompleteRowWitness hom challenges gamma (sourceValue row) (counts row) row (fallback row) (baseValue row) (values row)) ∧
        (∀ group : Fin 2, ((List.finRange Airbender.Compiler.MaterializedNative.KeccakUncached.native.model.imported.data.length).map
          (fun row => (outputPorts group).value (values row))).sum.numerator = 0) ∧
        ∀ row, FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.environment (baseValue row) (data row)) (Airbender.Keccak.clockConstraints (p := babyBearModulus) Airbender.Compiler.CleanClosedNative.KeccakUncached.nativeSetup) := by
  obtain ⟨counts, constructed⟩ := Airbender.Compiler.FramedWitnessNative.KeccakUncached.complete_trace_extends sourceValue original clockValid primitives authored fallback
  refine ⟨counts, ?_⟩
  intro R _ hom challenges gamma
  obtain ⟨baseValue, values, correct, cancel⟩ := constructed hom challenges gamma
  refine ⟨baseValue, values, correct, cancel, ?_⟩
  intro row
  have witness := (correct row).1
  rcases witness with ⟨inputsAt, arithmetic, _, _, _, _, _, _, helpers, _⟩
  exact Airbender.Compiler.CleanClosedNative.KeccakUncached.retained_clock_from_source (sourceValue row) (counts row) (baseValue row) (data row)
    inputsAt arithmetic helpers (authored row)

end Airbender.Compiler.CleanWitnessNative.KeccakUncached
