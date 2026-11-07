import Tests.PathGConsumedMessage.Data
import Tests.PathGLoopInputs

namespace Tests.PathGConsumedMessage
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
open Tests.PathGLoopProgram
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

/-- The changed ROM word is below the entire tracked RAM domain. -/
theorem ram_zero (address : BitVec 32) (member : Cell.ram address ∈ PathGLoopNative.cells) :
    (Cell.ram address).read before = .ok 0 before := by
  have scope := PathGLoopNative.ram_scope address member
  exact written_word_disjoint 152 0x0225a023 (Or.inr (by
    dsimp [ROM.limit] at scope
    omega))
    (initial_ram_above_code .protectedMessage address scope.2 (by
      dsimp [ROM.limit] at scope
      omega))

private theorem register_read_after_word {state : State} {index : BitVec 5}
    {value : BitVec 32} (address : Nat) (word : BitVec 32)
    (read : (Cell.register index).read state = .ok value state) :
    (Cell.register index).read (wordWriteState state address word) =
      .ok value (wordWriteState state address word) :=
  rX_register_frame (by rfl) index read

theorem cell_zero (cell : Cell) (member : cell ∈ PathGLoopNative.cells) :
    cell.read before = .ok 0 before := by
  cases cell with
  | register index =>
    exact register_read_after_word 152 0x0225a023
      (PathGLoopProgram.registers_zero .protectedMessage index)
  | ram address => exact ram_zero address member

theorem initialization :
    initialImage (p := babyBearModulus) before PathGLoopNative.cells =
      some (PathGLoopNative.cells.map PathGLoopNative.old) := by
  have allZero (domain : List Cell)
      (reads : ∀ cell ∈ domain, cell.read before = .ok 0 before) :
      initialImage (p := babyBearModulus) before domain =
        some (domain.map PathGLoopNative.old) := by
    induction domain with
    | nil => rfl
    | cons cell rest ih =>
      have next := ih (fun item member => reads item (List.mem_cons_of_mem cell member))
      simp only [initialImage] at next
      simp only [initialImage, List.mapM_cons, reads cell List.mem_cons_self, bind, Option.bind,
        next, List.map_cons, PathGLoopNative.old]
      rfl
  exact allZero PathGLoopNative.cells cell_zero

private theorem source (index : Fin 10) :
    (if (ordinaryEntry .protectedMessage index).pc = 152 then storeEntry
      else ordinaryEntry .protectedMessage index).SourceWith before UnifiedReduced.decoderFields := by
  by_cases same : (ordinaryEntry .protectedMessage index).pc = 152
  · rw [if_pos same]
    exact ⟨written_word_read _ 152 0x0225a023, rfl, rfl⟩
  · rw [if_neg same]
    refine ⟨?_, original_decode .protectedMessage (ordinaryCodeIndex index) before,
      ordinary_fields .protectedMessage index⟩
    apply written_word_disjoint 152 0x0225a023 ?_
      (fetch .protectedMessage (ordinaryCodeIndex index))
    fin_cases index <;> first | contradiction | decide +kernel

private theorem program_image_of_entries {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind)) (state : State)
    (entries : List (ProgramEntry Kind))
    (built : ∀ entry ∈ entries,
      programEntryRunWith projection state entry.pc = some entry) :
    programImageRunWith projection state (entries.map ProgramEntry.pc) = some entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    have tail := ih (fun item member => built item (List.mem_cons_of_mem entry member))
    change (rest.map ProgramEntry.pc).mapM (programEntryRunWith projection state) = some rest at tail
    change ((entry :: rest).map ProgramEntry.pc).mapM
      (programEntryRunWith projection state) = some (entry :: rest)
    rw [List.map_cons, List.mapM_cons, built entry List.mem_cons_self]
    simp only [bind, Option.bind]
    rw [tail]
    rfl

theorem ordinary_image : UnifiedReduced.Mixed.programImage before
    [0, 4, 8, 12, 16, 20, 132, 144, 148, 152] = some ordinaryProgram := by
  have built := program_image_of_entries UnifiedReduced.Mixed.decoderFields before ordinaryProgram (by
    intro entry member
    obtain ⟨old, included, rfl⟩ := List.mem_map.mp member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp included
    have nativeSource := source index
    have mixedFields : UnifiedReduced.Mixed.decoderFields
        (if (ordinaryEntry .protectedMessage index).pc = 152 then storeEntry
          else ordinaryEntry .protectedMessage index).instruction =
        some (if (ordinaryEntry .protectedMessage index).pc = 152 then storeEntry
          else ordinaryEntry .protectedMessage index).data := by
      unfold UnifiedReduced.Mixed.decoderFields
      rw [nativeSource.fields]
      rfl
    exact Trace.Proofs.program_entry_run_of_reads _ _ _ _ _ _
      nativeSource.bytes nativeSource.decoded mixedFields)
  have pcs : ordinaryProgram.map ProgramEntry.pc =
      [0, 4, 8, 12, 16, 20, 132, 144, 148, 152] := by decide +kernel
  rw [pcs] at built
  exact built

private theorem caller_source (index : Fin 2) :
    (callerEntry index).SourceWith before Delegation.Caller.decoderFields := by
  fin_cases index
  · exact ⟨written_word_disjoint 152 0x0225a023 (by decide +kernel)
        (fetch .protectedMessage 6),
      original_decode .protectedMessage 6 before, Tests.DelegationCaller.metadata .blakeG⟩
  · exact ⟨written_word_disjoint 152 0x0225a023 (by decide +kernel)
        (fetch .protectedMessage 11),
      original_decode .protectedMessage 11 before, Tests.DelegationCaller.metadata .blakeG⟩

private theorem caller_entry_run (index : Fin 2) :
    programEntryRunWith Delegation.Caller.decoderFields before (callerEntry index).pc =
      some (callerEntry index) :=
  Trace.Proofs.program_entry_run_of_reads _ _ _ _ _ _
    (caller_source index).bytes (caller_source index).decoded (caller_source index).fields

theorem caller_image : UnifiedReduced.Caller.programImage before [128, 156] = some callerProgram := by
  change programImageRunWith Delegation.Caller.decoderFields before
    [(callerEntry 0).pc, (callerEntry 1).pc] = _
  simp only [programImageRunWith, List.mapM_cons, List.mapM_nil,
    caller_entry_run 0, caller_entry_run 1, bind, Option.bind, pure]
  rfl

end Tests.PathGConsumedMessage
