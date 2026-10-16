import Tests.DelegationCaller
import Tests.DelegationMemory
import Airbender.Proofs.Delegation.SharedMemory
import Airbender.Proofs.Trace.ImageFrame

set_option Elab.async false

namespace Tests.DelegationSharedMemory
open Airbender Delegation Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def assignment (source : Nat) (i : Nat) : ZMod babyBearModulus :=
  if i = 35 then 4 else if i = 25 then source else Tests.DelegationCaller.assignment .keccak i
private def caller (source : Nat) : Trace.Row babyBearModulus PooledFamily := ⟨.addSub, assignment source⟩
private def cells : List Cell := .register 0 :: Tests.DelegationMemory.cells
private def machine (source : Nat) : PooledTrace babyBearModulus where
  rows := [caller source]
  rom := ⟨{ name := "unused", Contains _ _ := False }, { name := "unused", Contains _ _ := False }⟩
  initial := (caller source).start
  terminal := (caller source).finish
  initialMemory := (Cell.register 0).initialToken 0 :: Tests.DelegationMemory.data.initial
  terminalMemory := Caller.destinationToken (assignment source) :: Tests.DelegationMemory.data.terminal
private def data (source : Nat) : Caller.RequestTrace babyBearModulus :=
  ⟨machine source, Tests.DelegationMemory.data, [Tests.DelegationCaller.entry .keccak]⟩
private def before : State :=
  wordWriteState Tests.DelegationMemory.before 0 (Tests.DelegationCaller.entry .keccak).bits

private theorem caller_constraints (source : Fin 2) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment source.val)) AddSub.clockConstraints := by
  apply Verification.holds_append
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · fin_cases source <;> decide +kernel
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 6 := by simpa only [AddSub.lookup_count] using bound
      interval_cases i
      all_goals apply Verification.range16_contains
      all_goals fin_cases source <;> decide +kernel
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [AddSub.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals fin_cases source <;> decide +kernel

private theorem checks : Caller.RequestChecks (data 0) := by
  constructor
  · intro row member
    have same : row = caller 0 := List.mem_singleton.mp member
    subst row
    exact caller_constraints 0
  · intro row member
    have same : row = caller 0 := List.mem_singleton.mp member
    subst row
    decide +kernel
  · exact List.Perm.swap _ _ []
  · intro row member
    have same : row = caller 0 := List.mem_singleton.mp member
    subst row
    change ∃ i : Fin 1, Caller.nativeQuery (assignment 0) = Caller.query ([Tests.DelegationCaller.entry .keccak].get i)
    exact ⟨0, by decide +kernel⟩
  · exact Tests.DelegationMemory.accepted.constraints
  · intro row member
    have only : row = Tests.DelegationMemory.data.rows[0] := by
      simpa only [data, Tests.DelegationMemory.data, List.mem_singleton, List.getElem_cons_zero] using member
    subst row
    decide +kernel
  · have same : (data 0).calls = (data 0).fulfillments := by decide +kernel
    rw [← same]
    exact List.perm_append_comm

private theorem accepted : Caller.SharedMemoryAccepted (data 0) := by
  refine ⟨checks, rfl, ?_⟩
  decide +kernel

private theorem initialized : initialImage before cells = some (data 0).machine.initialMemory := by
  have image : initialImage before Tests.DelegationMemory.cells = some Tests.DelegationMemory.data.initial := by
    apply Trace.Proofs.image_frame Tests.DelegationMemory.inputs.initialization
    intro cell member value read
    cases cell with
    | register index => exact rX_register_frame (before := Tests.DelegationMemory.before) (after := before) rfl index read
    | ram address =>
      have lower : 4 ≤ address.toNat := by
        simp only [Tests.DelegationMemory.cells, List.mem_cons, List.not_mem_nil, or_false,
          Cell.ram.injEq, reduceCtorEq, false_or] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals decide +kernel
      exact written_word_disjoint 0 _ (Or.inr lower) read
  change List.mapM _ (.register 0 :: Tests.DelegationMemory.cells) = _
  rw [List.mapM_cons]
  change Option.bind (some ((Cell.register 0).initialToken (p := babyBearModulus) 0))
    (fun token => Option.bind (initialImage before Tests.DelegationMemory.cells)
      (fun rest => some (token :: rest))) = _
  rw [image]
  rfl

private theorem inputs (source : Nat) : Caller.SharedMemoryInputs (data source) before [0] cells := by
  constructor
  · constructor
    · have bytes : (Cell.ram 0).read before = .ok (Tests.DelegationCaller.entry .keccak).bits before :=
        written_word_read Tests.DelegationMemory.before 0 _
      have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .keccak).bits) before =
          .ok (Tests.DelegationCaller.entry .keccak).instruction before :=
        Tests.DelegationCaller.original_decoder .keccak before
      have fields : Caller.decoderFields (Tests.DelegationCaller.entry .keccak).instruction =
          some (Tests.DelegationCaller.entry .keccak).data := Tests.DelegationCaller.metadata .keccak
      simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
      rfl
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · change 4 % 4 = 0
      rfl
  · exact initialized
  · decide +kernel
  · intro cell member
    simp only [cells, Tests.DelegationMemory.cells, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Cell.Aligned]

theorem actual_shared_memory : Caller.SharedMemoryEffects (data 0) before cells :=
  Caller.shared_memory_soundness (by decide) (by decide) (by decide) accepted (inputs 0)

theorem native_source_zero : (Caller.sourceToken (assignment 0)).value = 0 :=
  actual_shared_memory.sources _ (by change caller 0 ∈ [caller 0]; simp)

theorem changed_source_locally_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment 1)) AddSub.clockConstraints :=
  caller_constraints 1

theorem changed_source_shared_matching_rejected : ¬ Caller.SharedMemoryAccepted (data 1) := by
  intro bad
  have publicState : Caller.SharedMemoryInputs (data 1) before [0] cells := inputs 1
  have requests := Caller.Proofs.request_binding_checks (by decide) (by decide) (by decide)
    bad.toRequestChecks publicState.publicProgram
  have zero := Caller.Proofs.shared_source_values (by decide) (by decide) bad publicState requests
    (caller 1) (by change caller 1 ∈ [caller 1]; simp)
  change Nat.pair 1 0 = 0 at zero
  norm_num [Nat.pair] at zero

end Tests.DelegationSharedMemory
