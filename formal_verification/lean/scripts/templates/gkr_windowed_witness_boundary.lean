
theorem canonical_old_witness (publicTops : Nat → Nat) {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin @BASE@.inputs.length → Source.BaseField) (counts : Fin 3 → Source.BaseField)
    (row : Fin @MODEL@.imported.data.length) (baseValue : GKRAddress → Source.BaseField)
    (witness : ActualRowWitness publicTops hom challenges gamma sourceValue counts row baseValue
      (canonical publicTops hom challenges gamma baseValue)) :
    RowWitness hom challenges gamma sourceValue counts row baseValue
      (@OLD@.canonical hom challenges gamma baseValue) := by
  rcases witness with ⟨inputsAt, arithmetic, _, _, _, _, countsAt, setupAt, helpers, outputs⟩
  refine ⟨inputsAt, arithmetic, @OLD@.canonical_base hom challenges gamma baseValue,
    @OLD@.canonical_affines hom challenges gamma baseValue arithmetic,
    @OLD@.canonical_lookups hom challenges gamma baseValue,
    @OLD@.canonical_products hom challenges gamma baseValue, countsAt, setupAt, helpers, ?_⟩
  unfold OutputsPreserved at outputs ⊢
  change
    RationalPair.mk (canonical publicTops hom challenges gamma baseValue (.InnerLayer 4 4)) (canonical publicTops hom challenges gamma baseValue (.InnerLayer 4 5)) = _ ∧
    RationalPair.mk (canonical publicTops hom challenges gamma baseValue (.InnerLayer 4 0)) (canonical publicTops hom challenges gamma baseValue (.InnerLayer 4 1)) = _ ∧
    RationalPair.mk (canonical publicTops hom challenges gamma baseValue (.InnerLayer 4 2)) (canonical publicTops hom challenges gamma baseValue (.InnerLayer 4 3)) = _ at outputs
  rw [GenericLookup_output0_unchanged publicTops hom challenges gamma baseValue,
    GenericLookup_output1_unchanged publicTops hom challenges gamma baseValue,
    Lookup16Bits_output0_unchanged publicTops hom challenges gamma baseValue,
    Lookup16Bits_output1_unchanged publicTops hom challenges gamma baseValue,
    LookupTimestamps_output0_unchanged publicTops hom challenges gamma baseValue,
    LookupTimestamps_output1_unchanged publicTops hom challenges gamma baseValue] at outputs
  exact outputs

def BoundaryOutputsPreserved (publicTops : Nat → Nat) {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (sourceValue : Fin @BASE@.inputs.length → Source.BaseField) (fallback baseValue : GKRAddress → Source.BaseField)
    (values : GKRAddress → R) : Prop :=
  values (.InnerLayer 4 8) = (((List.finRange 2).map (fun set => windowedBoundaryToken
    (@MEMORY@.sourceValues baseValue) publicTops .terminal set.val 512)).map (memoryTokenFingerprint hom challenges)).prod ∧
  values (.InnerLayer 4 9) = (((List.finRange 2).map (fun set => windowedBoundaryToken
    (@MEMORY@.sourceValues baseValue) publicTops .initial set.val 512)).map (memoryTokenFingerprint hom challenges)).prod ∧
  values (.InnerLayer 4 6) = maskProduct (hom (@MEMORY@.sourceExecute.value (@FRAME_MEMORY@.sourceMemoryValues sourceValue fallback)))
    ((@MEMORY@.memoryReadRows.map (fun entry => entry.fingerprint (@FRAME_MEMORY@.sourceMemoryValues sourceValue fallback) hom challenges)).prod) ∧
  values (.InnerLayer 4 7) = maskProduct (hom (@MEMORY@.sourceExecute.value (@FRAME_MEMORY@.sourceMemoryValues sourceValue fallback)))
    ((@MEMORY@.memoryWriteRows.map (fun entry => entry.fingerprint (@FRAME_MEMORY@.sourceMemoryValues sourceValue fallback) hom challenges)).prod)

def CompleteActualRowWitness (publicTops : Nat → Nat) {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin @BASE@.inputs.length → Source.BaseField) (counts : Fin 3 → Source.BaseField)
    (row : Fin @MODEL@.imported.data.length) (fallback baseValue : GKRAddress → Source.BaseField)
    (values : GKRAddress → R) : Prop :=
  ActualRowWitness publicTops hom challenges gamma sourceValue counts row baseValue values ∧
  (∀ address, addressEqual (@BASE@.bank.address (@BASE@.bank.placement address)) address = false →
    baseValue address = @MODEL@.baseOracle row fallback address) ∧
  BoundaryOutputsPreserved publicTops hom challenges sourceValue fallback baseValue values

theorem complete_row_extends (publicTops : Nat → Nat) {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin @BASE@.inputs.length → Source.BaseField)
    (original : Satisfies (@CONTRACT@.originals.map Expression.polynomial) sourceValue)
    (clockValid : Source.clockContract @CONTRACT@.clock (@BASE@.helperPlacement.memory.project sourceValue))
    (primitives : @HELPER@.profile.ExecutionValid (@HELPER@.execute.value (@BASE@.helperPlacement.memory.project sourceValue))
      (@BASE@.helperPlacement.memory.project sourceValue))
    (counts : Fin 3 → Source.BaseField) (row : Fin @MODEL@.imported.data.length)
    (fallback : GKRAddress → Source.BaseField) :
    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      CompleteActualRowWitness publicTops hom challenges gamma sourceValue counts row fallback baseValue values := by
  obtain ⟨baseValue, values, witness, canonicalEq, externalAgreement⟩ :=
    graph_extends publicTops hom challenges gamma sourceValue original clockValid primitives counts row fallback
  subst values
  have oldWitness := canonical_old_witness publicTops hom challenges gamma sourceValue counts row baseValue witness
  have memory := @FRAME@.memory_outputs_preserved hom challenges gamma sourceValue counts row fallback
    baseValue _ oldWitness externalAgreement
  refine ⟨baseValue, _, witness, externalAgreement,
    canonical_read_tokens publicTops hom challenges gamma baseValue,
    canonical_write_tokens publicTops hom challenges gamma baseValue, ?_, ?_⟩
  · rw [PermutationProduct_output0_unchanged publicTops hom challenges gamma baseValue]
    exact memory.2.2.1
  · rw [PermutationProduct_output1_unchanged publicTops hom challenges gamma baseValue]
    exact memory.2.2.2
