import Airbender.Proofs.GKRProtocol.WorkerPortChecks.BlakeRoundCached.Certificate

namespace Airbender.Compiler.WorkerPortsNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536

theorem original_columns : originalIndices.all (fun index =>
    decide (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement index) =
      Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement.original index))) = true := Airbender.Compiler.WorkerPortChecks.BlakeRoundCached.facts.1.1

theorem history_columns : (List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).all historyPredicate = true := Airbender.Compiler.WorkerPortChecks.BlakeRoundCached.facts.1.2

theorem historyPart0Item0 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨0, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart0Item1 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨1, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart0Item2 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨2, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart0Item3 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨3, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

noncomputable def historyPart0Block := ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).drop 0).take 4

theorem historyPart0 : historyPart0Block.all historyPredicate = true := by
  apply List.all_eq_true.mpr
  intro index member
  apply List.all_eq_true.mp history_columns index
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem historyPart4Item4 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨4, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart4Item5 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨5, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart4Item6 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨6, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart4Item7 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨7, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

noncomputable def historyPart4Block := ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).drop 4).take 4

theorem historyPart4 : historyPart4Block.all historyPredicate = true := by
  apply List.all_eq_true.mpr
  intro index member
  apply List.all_eq_true.mp history_columns index
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem historyPart8Item8 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨8, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart8Item9 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨9, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart8Item10 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨10, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart8Item11 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨11, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

noncomputable def historyPart8Block := ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).drop 8).take 4

theorem historyPart8 : historyPart8Block.all historyPredicate = true := by
  apply List.all_eq_true.mpr
  intro index member
  apply List.all_eq_true.mp history_columns index
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem historyPart12Item12 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨12, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart12Item13 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨13, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart12Item14 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨14, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart12Item15 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨15, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

noncomputable def historyPart12Block := ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).drop 12).take 4

theorem historyPart12 : historyPart12Block.all historyPredicate = true := by
  apply List.all_eq_true.mpr
  intro index member
  apply List.all_eq_true.mp history_columns index
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem historyPart16Item16 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨16, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart16Item17 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨17, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart16Item18 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨18, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart16Item19 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨19, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

noncomputable def historyPart16Block := ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).drop 16).take 4

theorem historyPart16 : historyPart16Block.all historyPredicate = true := by
  apply List.all_eq_true.mpr
  intro index member
  apply List.all_eq_true.mp history_columns index
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem historyPart20Item20 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨20, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart20Item21 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨21, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart20Item22 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨22, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart20Item23 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨23, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

noncomputable def historyPart20Block := ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).drop 20).take 4

theorem historyPart20 : historyPart20Block.all historyPredicate = true := by
  apply List.all_eq_true.mpr
  intro index member
  apply List.all_eq_true.mp history_columns index
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem historyPart24Item24 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨24, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart24Item25 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨25, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart24Item26 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨26, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart24Item27 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨27, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

noncomputable def historyPart24Block := ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).drop 24).take 4

theorem historyPart24 : historyPart24Block.all historyPredicate = true := by
  apply List.all_eq_true.mpr
  intro index member
  apply List.all_eq_true.mp history_columns index
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem historyPart28Item28 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨28, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart28Item29 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨29, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart28Item30 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨30, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart28Item31 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨31, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

noncomputable def historyPart28Block := ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).drop 28).take 4

theorem historyPart28 : historyPart28Block.all historyPredicate = true := by
  apply List.all_eq_true.mpr
  intro index member
  apply List.all_eq_true.mp history_columns index
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem historyPart32Item32 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨32, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart32Item33 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨33, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart32Item34 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨34, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart32Item35 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨35, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

noncomputable def historyPart32Block := ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).drop 32).take 4

theorem historyPart32 : historyPart32Block.all historyPredicate = true := by
  apply List.all_eq_true.mpr
  intro index member
  apply List.all_eq_true.mp history_columns index
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem historyPart36Item36 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨36, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart36Item37 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨37, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart36Item38 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨38, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart36Item39 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨39, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

noncomputable def historyPart36Block := ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).drop 36).take 4

theorem historyPart36 : historyPart36Block.all historyPredicate = true := by
  apply List.all_eq_true.mpr
  intro index member
  apply List.all_eq_true.mp history_columns index
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem historyPart40Item40 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨40, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart40Item41 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨41, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

theorem historyPart40Item42 : historyPredicate ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).get ⟨42, by decide +kernel⟩) = true :=
  List.all_eq_true.mp history_columns _ (List.get_mem _ _)

noncomputable def historyPart40Block := ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).drop 40).take 3

theorem historyPart40 : historyPart40Block.all historyPredicate = true := by
  apply List.all_eq_true.mpr
  intro index member
  apply List.all_eq_true.mp history_columns index
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem source_read_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows.map (fun row => row.token (logicalValues assignment other))) =
      Airbender.Blake2Round.importedConstraintsMemoryPorts.toList.map (Trace.readToken assignment) ++
        [(Delegation.Requests.fulfillment (⟨.blakeRound, assignment⟩ : Delegation.Row babyBearModulus)).issued] := by
  simp [Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows, Source.MemoryRow.token,
    Source.MemoryField.value, Source.LookupInput.value, logicalValues, Trace.readToken, Trace.rawPair,
    Trace.MemoryPort.readCode, Trace.WordColumns.code, Trace.WordColumns.evaluate, Trace.MemoryAddress.code,
    Verification.IndirectPort.rawAddress, Delegation.Requests.fulfillment,
    Delegation.Requests.csr, Delegation.Row.columns, Delegation.Requests.Request.issued,
    Delegation.Requests.Request.token, Airbender.Blake2Round.importedConstraintsMemoryPorts,
    Airbender.Blake2Round.importedConstraintsDelegationColumns]
  all_goals decide +kernel

theorem source_write_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows.map (fun row => row.token (logicalValues assignment other))) =
      Airbender.Blake2Round.importedConstraintsMemoryPorts.toList.map ((⟨.blakeRound, assignment⟩ : Delegation.Row babyBearModulus).writeToken) ++
        [(Delegation.Requests.fulfillment (⟨.blakeRound, assignment⟩ : Delegation.Row babyBearModulus)).empty] := by
  simp [Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows, Source.MemoryRow.token,
    Source.MemoryField.value, Source.LookupInput.value, logicalValues, Delegation.Row.writeToken, Trace.rawPair,
    Trace.MemoryPort.writeCode, Trace.WordColumns.code, Trace.WordColumns.evaluate, Trace.MemoryAddress.code,
    Verification.IndirectPort.rawAddress, Delegation.Requests.fulfillment,
    Delegation.Requests.csr, Delegation.Row.columns, Delegation.Requests.Request.empty,
    Delegation.Requests.Request.token, Airbender.Blake2Round.importedConstraintsMemoryPorts,
    Airbender.Blake2Round.importedConstraintsDelegationColumns]
  all_goals decide +kernel

theorem original_assignment (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (index : Nat) (used : index ∈ originalIndices) :
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical).original index =
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get index := by
  exact (congrArg physical (of_decide_eq_true (List.all_eq_true.mp original_columns index used))).symm

theorem history_assignment (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (index : Fin Airbender.Blake2Round.importedConstraintsMemoryPorts.size) (limb : Fin 2) :
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical).readTimestamp index.val limb =
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get
        ((Airbender.Blake2Round.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val]) := by
  exact (congrArg physical (of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp history_columns index (List.mem_finRange index)) limb (List.mem_finRange limb)))).symm

theorem history_indices :
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows).all
      (fun row => row.fields.all (fun field => field.historyIndices.all
        (fun index => decide (index.1 < Airbender.Blake2Round.importedConstraintsMemoryPorts.size)))) = true := Airbender.Compiler.WorkerPortChecks.BlakeRoundCached.facts.2

theorem row_token_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (row : Source.MemoryRow)
    (included : row ∈ Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows) :
    row.token (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical) =
      row.token (logicalValues (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get
        (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical)) := by
  apply Source.MemoryRow.token_congr
  intro field member
  apply Source.MemoryField.value_congr_scoped
  · intro index used
    apply original_assignment physical data index
    change index ∈ [0] ++ (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows).flatMap Source.MemoryRow.originalIndices
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨row, included, ?_⟩
    exact List.mem_flatMap.mpr ⟨field, member, used⟩
  · intro index used
    have bounded := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp
      (List.all_eq_true.mp history_indices row included) field member) index used)
    change _ = if guard : index.1 < Airbender.Blake2Round.importedConstraintsMemoryPorts.size then _ else 0
    rw [dif_pos bounded]
    exact history_assignment physical data ⟨index.1, bounded⟩ index.2
  · rfl
  · rfl
  · rfl

theorem read_tokens_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows.map (fun row => row.token (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical)) =
      Airbender.Blake2Round.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get) ++ [(Delegation.Requests.fulfillment (⟨.blakeRound, (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus)).issued] := by
  rw [← source_read_tokens (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical)]
  apply List.map_congr_left
  intro row member
  apply row_token_from_base
  exact List.mem_append_left _ member

theorem read_products_from_base {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical) hom challenges)).prod =
      ((Airbender.Blake2Round.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get) ++ [(Delegation.Requests.fulfillment (⟨.blakeRound, (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus)).issued]).map (memoryTokenFingerprint hom challenges)).prod := by
  rw [← Source.MemoryRow.token_products Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical) hom challenges,
    read_tokens_from_base physical data]

theorem write_tokens_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows.map (fun row => row.token (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical)) =
      Airbender.Blake2Round.importedConstraintsMemoryPorts.toList.map ((⟨.blakeRound, (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus).writeToken) ++ [(Delegation.Requests.fulfillment (⟨.blakeRound, (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus)).empty] := by
  rw [← source_write_tokens (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical)]
  apply List.map_congr_left
  intro row member
  apply row_token_from_base
  exact List.mem_append_right _ member

theorem write_products_from_base {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical) hom challenges)).prod =
      ((Airbender.Blake2Round.importedConstraintsMemoryPorts.toList.map ((⟨.blakeRound, (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus).writeToken) ++ [(Delegation.Requests.fulfillment (⟨.blakeRound, (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus)).empty]).map (memoryTokenFingerprint hom challenges)).prod := by
  rw [← Source.MemoryRow.token_products Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical) hom challenges,
    write_tokens_from_base physical data]

theorem read_output_logical {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.BlakeRoundCached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadOutput =
      maskProduct (hom ((Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get Airbender.Blake2Round.importedConstraintsDelegationColumns.execute))
      ((Airbender.Blake2Round.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get) ++ [(Delegation.Requests.fulfillment (⟨.blakeRound, (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus)).issued]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  let assignment : TypedAssignment R := ⟨physical, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.BlakeRoundCached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  have reduced := Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadSourceReduction hom challenges assignment defined (Airbender.Compiler.FunctionalLinksNative.BlakeRoundCached.native.memoryCopies physical arithmetic) holds
  rw [typedEq] at reduced
  change values Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadOutput = maskProduct (hom (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical)))
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical) hom challenges)).prod at reduced
  have executeSame : Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical) =
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get Airbender.Blake2Round.importedConstraintsDelegationColumns.execute :=
    original_assignment physical data 0 (List.mem_append_left _ (List.mem_cons_self))
  rw [executeSame, read_products_from_base hom challenges physical data] at reduced
  exact reduced

theorem write_output_logical {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.BlakeRoundCached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.BlakeRoundCached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteOutput =
      maskProduct (hom ((Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get Airbender.Blake2Round.importedConstraintsDelegationColumns.execute))
      ((Airbender.Blake2Round.importedConstraintsMemoryPorts.toList.map ((⟨.blakeRound, (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus).writeToken) ++ [(Delegation.Requests.fulfillment (⟨.blakeRound, (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus)).empty]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  let assignment : TypedAssignment R := ⟨physical, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.BlakeRoundCached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  have reduced := Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteSourceReduction hom challenges assignment defined (Airbender.Compiler.FunctionalLinksNative.BlakeRoundCached.native.memoryCopies physical arithmetic) holds
  rw [typedEq] at reduced
  change values Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteOutput = maskProduct (hom (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical)))
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical) hom challenges)).prod at reduced
  have executeSame : Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourceValues physical) =
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical data).get Airbender.Blake2Round.importedConstraintsDelegationColumns.execute :=
    original_assignment physical data 0 (List.mem_append_left _ (List.mem_cons_self))
  rw [executeSame, write_products_from_base hom challenges physical data] at reduced
  exact reduced

end Airbender.Compiler.WorkerPortsNative.BlakeRoundCached
