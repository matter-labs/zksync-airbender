import GKRProtocol.InitializationWindowImport
import GKRProtocol.FunctionalNative.UnifiedUncached

namespace Airbender.Compiler.WindowedNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

import_initialization_windows native from "artifacts/compiler/unified-uncached.json"

theorem shape0 (publicTops : Nat → Nat) :
    (nativeGate0 publicTops).functional.outputs = Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step4.outputs ∧
    (nativeGate0 publicTops).functional.inputs = Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step4.inputs := by exact ⟨rfl, rfl⟩

theorem shape1 (publicTops : Nat → Nat) :
    (nativeGate1 publicTops).functional.outputs = Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step5.outputs ∧
    (nativeGate1 publicTops).functional.inputs = Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step5.inputs := by exact ⟨rfl, rfl⟩

theorem specialization0 : nativeGate0 id = Airbender.Compiler.ProductNative.UnifiedUncached.native.gate4 := by rfl

theorem specialization1 : nativeGate1 id = Airbender.Compiler.ProductNative.UnifiedUncached.native.gate5 := by rfl

noncomputable def program (publicTops : Nat → Nat) : FunctionalProgram :=
  [Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step0, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step1, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step2, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step3, (nativeGate0 publicTops).functional, (nativeGate1 publicTops).functional, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step6, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step7, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step8, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step9, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step10, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step11, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step12, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step13, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step14, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step15, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step16, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step17, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step18, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step19, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step20, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step21, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step22, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step23, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step24, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step25, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step26, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step27, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step28, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step29, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step30, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step31, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step32, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step33, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step34, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step35, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step36, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step37, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step38, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step39, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step40, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step41, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step42, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step43, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step44, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step45, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step46, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step47, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step48, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step49, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.step50]

theorem program_shape (publicTops : Nat → Nat) :
    List.Forall₂ (fun first second => second.outputs = first.outputs ∧ second.inputs = first.inputs) Airbender.Compiler.FunctionalNative.UnifiedUncached.native.program (program publicTops) := by
  exact List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (shape0 publicTops) (List.Forall₂.cons (shape1 publicTops) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.cons (⟨rfl, rfl⟩) (List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))))))))))))

theorem valid (publicTops : Nat → Nat) : (program publicTops).Valid Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase [] :=
  Airbender.Compiler.FunctionalNative.UnifiedUncached.native.valid.replace (program_shape publicTops)

noncomputable def canonical {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R) (physical : GKRAddress → Source.BaseField) : GKRAddress → R :=
  Functional.read Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase (hom ∘ physical)
    ((program publicTops).execute hom challenges gamma Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase (hom ∘ physical) (fun _ => 0))

theorem canonical_steps {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R) (physical : GKRAddress → Source.BaseField) :
    ∀ step ∈ program publicTops, step.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=
  (FunctionalProgram.execute_sound (valid publicTops) hom challenges gamma (hom ∘ physical) (fun _ => 0)).1

end Airbender.Compiler.WindowedNative.UnifiedUncached
