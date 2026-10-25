import GKRProtocol.WindowedNative.UnifiedUncached
import GKRProtocol.WindowedInitialization
import GKRProtocol.MemoryNative.UnifiedUncached

namespace Airbender.Compiler.WindowedNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem gate0_tokens {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase address = true → values address = hom (physical address))
    (holds : (nativeGate0 publicTops).Holds hom challenges values) :
    values (.InnerLayer 1 5) =
      (((List.finRange 2).map (fun set => windowedBoundaryToken
        (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) publicTops .initial set.val 512)).map
          (memoryTokenFingerprint hom challenges)).prod := by
  change _ = memoryTokenFingerprint hom challenges (windowedBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) publicTops .initial 0 512) *
    (memoryTokenFingerprint hom challenges (windowedBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) publicTops .initial 1 512) * 1)
  rw [mul_one, windowed_initial_fingerprint, windowed_initial_fingerprint]
  change _ = _ * _ at holds
  simp only [AffineProgram.value, LookupPayload.interpret, AffineProgram.mapCoefficients, CacheCoefficient.value] at holds
  have low : (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).initializationAddress 0 = physical (.VirtualSetup .InitsAndTeardownsLow) := by rfl
  have high : (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).initializationAddress 1 = physical (.VirtualSetup .InitsAndTeardownsHigh) := by rfl
  rw [low, high]
  rw [holds]
  rw [baseLaw (.VirtualSetup .InitsAndTeardownsLow) (by decide +kernel)]
  rw [baseLaw (.VirtualSetup .InitsAndTeardownsHigh) (by decide +kernel)]
  simp only [Nat.cast_one, map_one]
  rfl

theorem gate1_tokens {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase address = true → values address = hom (physical address))
    (holds : (nativeGate1 publicTops).Holds hom challenges values) :
    values (.InnerLayer 1 6) =
      (((List.finRange 2).map (fun set => windowedBoundaryToken
        (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) publicTops .terminal set.val 512)).map
          (memoryTokenFingerprint hom challenges)).prod := by
  change _ = memoryTokenFingerprint hom challenges (windowedBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) publicTops .terminal 0 512) *
    (memoryTokenFingerprint hom challenges (windowedBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) publicTops .terminal 1 512) * 1)
  rw [mul_one, windowed_terminal_fingerprint, windowed_terminal_fingerprint]
  change _ = _ * _ at holds
  simp only [AffineProgram.value, LookupPayload.interpret, AffineProgram.mapCoefficients, CacheCoefficient.value] at holds
  have low : (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).initializationAddress 0 = physical (.VirtualSetup .InitsAndTeardownsLow) := by rfl
  have high : (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).initializationAddress 1 = physical (.VirtualSetup .InitsAndTeardownsHigh) := by rfl
  rw [low, high]
  rw [show (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).teardownTimestamp 0 0 = physical (.BaseLayerMemory 32) from rfl]
  rw [show (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).teardownTimestamp 0 1 = physical (.BaseLayerMemory 33) from rfl]
  rw [show (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).teardownValue 0 0 = physical (.BaseLayerMemory 30) from rfl]
  rw [show (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).teardownValue 0 1 = physical (.BaseLayerMemory 31) from rfl]
  rw [show (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).teardownTimestamp 1 0 = physical (.BaseLayerMemory 36) from rfl]
  rw [show (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).teardownTimestamp 1 1 = physical (.BaseLayerMemory 37) from rfl]
  rw [show (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).teardownValue 1 0 = physical (.BaseLayerMemory 34) from rfl]
  rw [show (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical).teardownValue 1 1 = physical (.BaseLayerMemory 35) from rfl]
  rw [holds]
  rw [baseLaw (.VirtualSetup .InitsAndTeardownsLow) (by decide +kernel)]
  rw [baseLaw (.VirtualSetup .InitsAndTeardownsHigh) (by decide +kernel)]
  rw [baseLaw (.BaseLayerMemory 32) (by decide +kernel)]
  rw [baseLaw (.BaseLayerMemory 33) (by decide +kernel)]
  rw [baseLaw (.BaseLayerMemory 30) (by decide +kernel)]
  rw [baseLaw (.BaseLayerMemory 31) (by decide +kernel)]
  rw [baseLaw (.BaseLayerMemory 36) (by decide +kernel)]
  rw [baseLaw (.BaseLayerMemory 37) (by decide +kernel)]
  rw [baseLaw (.BaseLayerMemory 34) (by decide +kernel)]
  rw [baseLaw (.BaseLayerMemory 35) (by decide +kernel)]
  simp only [Nat.cast_one, map_one]
  rfl

theorem read_output_tokens
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase address = true → values address = hom (physical address))
    (products : ∀ gate ∈ productGates publicTops, gate.Holds hom challenges values) :
    values (.InnerLayer 4 8) =
      (((List.finRange 2).map (fun set => windowedBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) publicTops .terminal set.val 512)).map (memoryTokenFingerprint hom challenges)).prod := by
  have copy22 := products Airbender.Compiler.ProductNative.UnifiedUncached.native.gate22 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))
  change values _ = values _ at copy22
  rw [copy22]
  have copy18 := products Airbender.Compiler.ProductNative.UnifiedUncached.native.gate18 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))
  change values _ = values _ at copy18
  rw [copy18]
  have copy10 := products Airbender.Compiler.ProductNative.UnifiedUncached.native.gate10 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))
  change values _ = values _ at copy10
  rw [copy10]
  exact gate1_tokens publicTops hom challenges physical values baseLaw (products (nativeGate1 publicTops) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))

theorem canonical_read_tokens {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    canonical publicTops hom challenges gamma physical (.InnerLayer 4 8) =
      (((List.finRange 2).map (fun set => windowedBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) publicTops .terminal set.val 512)).map (memoryTokenFingerprint hom challenges)).prod :=
  read_output_tokens publicTops hom challenges physical _ (canonical_base publicTops hom challenges gamma physical) (canonical_products publicTops hom challenges gamma physical)

theorem write_output_tokens
    {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.UnifiedUncached.native.isBase address = true → values address = hom (physical address))
    (products : ∀ gate ∈ productGates publicTops, gate.Holds hom challenges values) :
    values (.InnerLayer 4 9) =
      (((List.finRange 2).map (fun set => windowedBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) publicTops .initial set.val 512)).map (memoryTokenFingerprint hom challenges)).prod := by
  have copy23 := products Airbender.Compiler.ProductNative.UnifiedUncached.native.gate23 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))))))
  change values _ = values _ at copy23
  rw [copy23]
  have copy19 := products Airbender.Compiler.ProductNative.UnifiedUncached.native.gate19 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))))
  change values _ = values _ at copy19
  rw [copy19]
  have copy11 := products Airbender.Compiler.ProductNative.UnifiedUncached.native.gate11 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))
  change values _ = values _ at copy11
  rw [copy11]
  exact gate0_tokens publicTops hom challenges physical values baseLaw (products (nativeGate0 publicTops) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))

theorem canonical_write_tokens {R : Type} [CommRing R] (publicTops : Nat → Nat)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (physical : GKRAddress → Source.BaseField) :
    canonical publicTops hom challenges gamma physical (.InnerLayer 4 9) =
      (((List.finRange 2).map (fun set => windowedBoundaryToken (Airbender.Compiler.MemoryNative.UnifiedUncached.native.sourceValues physical) publicTops .initial set.val 512)).map (memoryTokenFingerprint hom challenges)).prod :=
  write_output_tokens publicTops hom challenges physical _ (canonical_base publicTops hom challenges gamma physical) (canonical_products publicTops hom challenges gamma physical)

end Airbender.Compiler.WindowedNative.UnifiedUncached
