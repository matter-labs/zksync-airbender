import Airbender.Proofs.GKRProtocol.MemoryValueCongruence
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.BigintUncached
import Airbender.Proofs.GKRProtocol.MemoryNative.BigintUncached
import Airbender.Proofs.GKRProtocol.MemoryTokens
import Airbender.Review.Helpers.Delegation.Requests

namespace Airbender.Compiler.WorkerPortsNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def originalIndices : List Nat := [0] ++
  (Airbender.Compiler.MemoryNative.BigintUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BigintUncached.native.memoryWriteRows).flatMap Source.MemoryRow.originalIndices

theorem original_columns : originalIndices.all (fun index =>
    decide (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement index) =
      Airbender.Compiler.MemoryNative.BigintUncached.native.bank.address (Airbender.Compiler.MemoryNative.BigintUncached.native.sourcePlacement.original index))) = true := by decide +kernel

theorem history_columns : ((List.finRange Airbender.Bigint.importedConstraintsMemoryPorts.size).all (fun index =>
    (List.finRange 2).all (fun limb => decide
      (Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement
        ((Airbender.Bigint.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val])) =
       Airbender.Compiler.MemoryNative.BigintUncached.native.bank.address (Airbender.Compiler.MemoryNative.BigintUncached.native.sourcePlacement.readTimestamp index.val limb))))) = true := by decide +kernel

noncomputable def logicalValues (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) : Source.MemoryValues :=
  { other with
    original := assignment
    readTimestamp := fun query limb =>
      if bounded : query < Airbender.Bigint.importedConstraintsMemoryPorts.size then
        assignment ((Airbender.Bigint.importedConstraintsMemoryPorts[query]).clock.previous[limb.val])
      else 0 }

theorem source_read_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :
    (Airbender.Compiler.MemoryNative.BigintUncached.native.memoryReadRows.map (fun row => row.token (logicalValues assignment other))) =
      Airbender.Bigint.importedConstraintsMemoryPorts.toList.map (Trace.readToken assignment) ++
        [(Delegation.Requests.fulfillment (⟨.bigint, assignment⟩ : Delegation.Row babyBearModulus)).issued] := by
  simp [Airbender.Compiler.MemoryNative.BigintUncached.native.memoryReadRows, Source.MemoryRow.token,
    Source.MemoryField.value, Source.LookupInput.value, logicalValues, Trace.readToken, Trace.rawPair,
    Trace.MemoryPort.readCode, Trace.WordColumns.code, Trace.WordColumns.evaluate, Trace.MemoryAddress.code,
    Verification.IndirectPort.rawAddress, Delegation.Requests.fulfillment,
    Delegation.Requests.csr, Delegation.Row.columns, Delegation.Requests.Request.issued,
    Delegation.Requests.Request.token, Airbender.Bigint.importedConstraintsMemoryPorts,
    Airbender.Bigint.importedConstraintsDelegationColumns]
  all_goals decide +kernel

theorem source_write_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :
    (Airbender.Compiler.MemoryNative.BigintUncached.native.memoryWriteRows.map (fun row => row.token (logicalValues assignment other))) =
      Airbender.Bigint.importedConstraintsMemoryPorts.toList.map ((⟨.bigint, assignment⟩ : Delegation.Row babyBearModulus).writeToken) ++
        [(Delegation.Requests.fulfillment (⟨.bigint, assignment⟩ : Delegation.Row babyBearModulus)).empty] := by
  simp [Airbender.Compiler.MemoryNative.BigintUncached.native.memoryWriteRows, Source.MemoryRow.token,
    Source.MemoryField.value, Source.LookupInput.value, logicalValues, Delegation.Row.writeToken, Trace.rawPair,
    Trace.MemoryPort.writeCode, Trace.WordColumns.code, Trace.WordColumns.evaluate, Trace.MemoryAddress.code,
    Verification.IndirectPort.rawAddress, Delegation.Requests.fulfillment,
    Delegation.Requests.csr, Delegation.Row.columns, Delegation.Requests.Request.empty,
    Delegation.Requests.Request.token, Airbender.Bigint.importedConstraintsMemoryPorts,
    Airbender.Bigint.importedConstraintsDelegationColumns]
  all_goals decide +kernel

theorem original_assignment (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (index : Nat) (used : index ∈ originalIndices) :
    (Airbender.Compiler.MemoryNative.BigintUncached.native.sourceValues physical).original index =
      (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data).get index := by
  exact (congrArg physical (of_decide_eq_true (List.all_eq_true.mp original_columns index used))).symm

theorem history_assignment (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (index : Fin Airbender.Bigint.importedConstraintsMemoryPorts.size) (limb : Fin 2) :
    (Airbender.Compiler.MemoryNative.BigintUncached.native.sourceValues physical).readTimestamp index.val limb =
      (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data).get
        ((Airbender.Bigint.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val]) := by
  exact (congrArg physical (of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp history_columns index (List.mem_finRange index)) limb (List.mem_finRange limb)))).symm

theorem history_indices :
    (Airbender.Compiler.MemoryNative.BigintUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BigintUncached.native.memoryWriteRows).all
      (fun row => row.fields.all (fun field => field.historyIndices.all
        (fun index => decide (index.1 < Airbender.Bigint.importedConstraintsMemoryPorts.size)))) = true := by decide +kernel

theorem row_token_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (row : Source.MemoryRow)
    (included : row ∈ Airbender.Compiler.MemoryNative.BigintUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BigintUncached.native.memoryWriteRows) :
    row.token (Airbender.Compiler.MemoryNative.BigintUncached.native.sourceValues physical) =
      row.token (logicalValues (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment physical data).get
        (Airbender.Compiler.MemoryNative.BigintUncached.native.sourceValues physical)) := by
  apply Source.MemoryRow.token_congr
  intro field member
  apply Source.MemoryField.value_congr_scoped
  · intro index used
    apply original_assignment physical data index
    change index ∈ [0] ++ (Airbender.Compiler.MemoryNative.BigintUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BigintUncached.native.memoryWriteRows).flatMap Source.MemoryRow.originalIndices
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨row, included, ?_⟩
    exact List.mem_flatMap.mpr ⟨field, member, used⟩
  · intro index used
    have bounded := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp
      (List.all_eq_true.mp history_indices row included) field member) index used)
    change _ = if guard : index.1 < Airbender.Bigint.importedConstraintsMemoryPorts.size then _ else 0
    rw [dif_pos bounded]
    exact history_assignment physical data ⟨index.1, bounded⟩ index.2
  · rfl
  · rfl
  · rfl

end Airbender.Compiler.WorkerPortsNative.BigintUncached
