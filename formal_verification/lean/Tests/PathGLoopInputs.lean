/- Public program images and zero initialization for the three G loop variants.
The proofs read the actual installed code and boot memory and keep native
acceptance and execution separate from the public input profile. -/
import Tests.PathGLoopNativeBase
import Airbender.Proofs.Sail.ZeroMemory
import Airbender.Proofs.Trace.ProgramConstruction

namespace Tests.PathGLoopProgram
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

private def CodeDisjoint (left right : CodeEntry) : Prop :=
  left.pc.toNat + 4 ≤ right.pc.toNat ∨ right.pc.toNat + 4 ≤ left.pc.toNat

private theorem install_preserves_read (entries : List CodeEntry) {state : State}
    {address : Nat} {value : BitVec 32}
    (apart : ∀ entry ∈ entries,
      address + 4 ≤ entry.pc.toNat ∨ entry.pc.toNat + 4 ≤ address)
    (read : (readBytes (ue := SailRV32.exception) 4 address).run state = .ok value state) :
    (readBytes (ue := SailRV32.exception) 4 address).run (install entries state) =
      .ok value (install entries state) := by
  induction entries generalizing state with
  | nil => exact read
  | cons entry rest ih =>
    exact ih (fun item member => apart item (List.mem_cons_of_mem entry member))
      (written_word_disjoint entry.pc.toNat entry.bits
        (apart entry List.mem_cons_self) read)

/-- Installing disjoint instruction windows reads back the exact written word.
Only the finite code list is inspected; the incoming memory is arbitrary. -/
private theorem install_fetch (entries : List CodeEntry) (entry : CodeEntry) (state : State)
    (apart : entries.Pairwise CodeDisjoint) (member : entry ∈ entries) :
    (readBytes (ue := SailRV32.exception) 4 entry.pc.toNat).run (install entries state) =
      .ok entry.bits (install entries state) := by
  induction entries generalizing state with
  | nil => cases member
  | cons first rest ih =>
    rcases List.pairwise_cons.mp apart with ⟨firstApart, restApart⟩
    rcases List.mem_cons.mp member with rfl | later
    · exact install_preserves_read rest firstApart
        (written_word_read state entry.pc.toNat entry.bits)
    · exact ih (wordWriteState state first.pc.toNat first.bits) restApart later

private theorem code_disjoint (variant : Variant) : (code variant).Pairwise CodeDisjoint := by
  change (code variant).Pairwise (fun left right =>
    left.pc.toNat + 4 ≤ right.pc.toNat ∨ right.pc.toNat + 4 ≤ left.pc.toNat)
  cases variant <;> decide +kernel

/-- Each of the twelve instruction words is obtained from its actual install. -/
theorem fetch (variant : Variant) (index : Fin 12) :
    (Cell.ram (codeEntry variant index).pc).read (before variant) =
      .ok (codeEntry variant index).bits (before variant) := by
  exact install_fetch (code variant) (codeEntry variant index) AirbenderInitialization.before
    (code_disjoint variant) (List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩)

private theorem install_registers (entries : List CodeEntry) (state : State) :
    (install entries state).regs = state.regs := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih => exact ih (wordWriteState state entry.pc.toNat entry.bits)

private theorem install_configuration (entries : List CodeEntry) {state : State}
    (configured : FlatMemoryConfiguration state) : FlatMemoryConfiguration (install entries state) := by
  induction entries generalizing state with
  | nil => exact configured
  | cons entry rest ih =>
    exact ih (configuration_word_write configured entry.pc.toNat entry.bits)

theorem configuration (variant : Variant) : FlatMemoryConfiguration (before variant) :=
  install_configuration (code variant) AirbenderInitialization.configuration

theorem registers_zero (variant : Variant) (index : BitVec 5) :
    (Cell.register index).read (before variant) = .ok 0 (before variant) :=
  rX_register_frame (install_registers (code variant) AirbenderInitialization.before) index
    (AirbenderInitialization.registers_zero index)

/-- Installing code preserves the actual zero initial architectural PC. -/
theorem initial_pc (variant : Variant) :
    run (SailRV32.Functions.get_arch_pc ()) (before variant) = .ok 0 (before variant) := by
  apply read_register
  rw [show (before variant).regs = AirbenderInitialization.before.regs from install_registers _ _]
  exact read_register_iff.mp AirbenderInitialization.standalone_profile.profile.pc

private theorem code_end (variant : Variant) (index : Fin 12) :
    (codeEntry variant index).pc.toNat + 4 ≤ 160 := by
  fin_cases index <;> cases variant <;> decide +kernel

/-- RAM words above all installed instruction windows retain their real zero
boot reads. The GiB image is treated symbolically through zeroMemory_word. -/
theorem initial_ram_above_code (variant : Variant) (address : BitVec 32)
    (bound : address.toNat + 4 ≤ 2 ^ 30) (above : 160 ≤ address.toNat) :
    (Cell.ram address).read (before variant) = .ok 0 (before variant) := by
  apply install_preserves_read (code variant)
  · intro entry member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    right
    have ending := code_end variant index
    omega
  · exact zeroMemory_word (before := AirbenderInitialization.before) rfl bound

theorem state_block_zero (variant : Variant) (index : Fin 16) :
    (Cell.ram (stateAddress + BitVec.ofNat 32 (4 * index.val))).read (before variant) =
      .ok 0 (before variant) := by
  apply initial_ram_above_code variant
  · fin_cases index <;> decide +kernel
  · fin_cases index <;> decide +kernel

theorem message_block_zero (variant : Variant) (index : Fin 16) :
    (Cell.ram (messageAddress + BitVec.ofNat 32 (4 * index.val))).read (before variant) =
      .ok 0 (before variant) := by
  apply initial_ram_above_code variant
  · fin_cases index <;> decide +kernel
  · fin_cases index <;> decide +kernel

theorem scratch_zero (variant : Variant) :
    (Cell.ram scratchAddress).read (before variant) = .ok 0 (before variant) :=
  initial_ram_above_code variant scratchAddress (by decide +kernel) (by decide +kernel)

/-- Original generated decoding and actual installed bytes for all ten
ordinary sites, including the selected variant at PC152. -/
theorem ordinary_source (variant : Variant) (index : Fin 10) :
    (ordinaryEntry variant index).SourceWith (before variant) UnifiedReduced.decoderFields :=
  ⟨fetch variant (ordinaryCodeIndex index),
    original_decode variant (ordinaryCodeIndex index) (before variant), ordinary_fields variant index⟩

end Tests.PathGLoopProgram

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

private theorem caller_source (variant : Variant) (index : Fin 2) :
    (callerEntry index).SourceWith (before variant) Delegation.Caller.decoderFields := by
  fin_cases index
  · exact ⟨PathGLoopProgram.fetch variant 6,
      original_decode variant 6 (before variant), Tests.DelegationCaller.metadata .blakeG⟩
  · exact ⟨PathGLoopProgram.fetch variant 11,
      original_decode variant 11 (before variant), Tests.DelegationCaller.metadata .blakeG⟩

private theorem caller_entry_run (variant : Variant) (index : Fin 2) :
    programEntryRunWith Delegation.Caller.decoderFields (before variant) (callerEntry index).pc =
      some (callerEntry index) :=
  Trace.Proofs.program_entry_run_of_reads _ _ _ _ _ _
    (caller_source variant index).bytes (caller_source variant index).decoded
    (caller_source variant index).fields

theorem caller_image (variant : Variant) :
    UnifiedReduced.Caller.programImage (before variant) [128, 156] = some callerProgram := by
  change programImageRunWith Delegation.Caller.decoderFields (before variant)
    [(callerEntry 0).pc, (callerEntry 1).pc] = _
  simp only [programImageRunWith, List.mapM_cons, List.mapM_nil,
    caller_entry_run variant 0, caller_entry_run variant 1, bind, Option.bind, pure]
  rfl

private theorem mixed_fields (variant : Variant) (index : Fin 10) :
    UnifiedReduced.Mixed.decoderFields (ordinaryEntry variant index).instruction =
      some (ordinaryEntry variant index).data := by
  unfold UnifiedReduced.Mixed.decoderFields
  rw [ordinary_fields]
  rfl

private theorem mixed_entry_run (variant : Variant) (index : Fin 10) :
    programEntryRunWith UnifiedReduced.Mixed.decoderFields (before variant)
      (ordinaryEntry variant index).pc = some (ordinaryEntry variant index) :=
  Trace.Proofs.program_entry_run_of_reads _ _ _ _ _ _
    (ordinary_source variant index).bytes (ordinary_source variant index).decoded
    (mixed_fields variant index)

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

theorem ordinary_image (variant : Variant) :
    UnifiedReduced.Mixed.programImage (before variant)
      [0, 4, 8, 12, 16, 20, 132, 144, 148, 152] = some (ordinaryProgram variant) := by
  have built := program_image_of_entries UnifiedReduced.Mixed.decoderFields (before variant)
    (ordinaryProgram variant) (by
      intro entry member
      rcases List.mem_map.mp member with ⟨index, _, rfl⟩
      exact mixed_entry_run variant index)
  have pcs : (ordinaryProgram variant).map ProgramEntry.pc =
      [0, 4, 8, 12, 16, 20, 132, 144, 148, 152] := by
    cases variant <;> rfl
  rw [pcs] at built
  exact built

private theorem cells_zero (variant : Variant) (cell : Cell) (member : cell ∈ cells) :
    cell.read (before variant) = .ok 0 (before variant) := by
  simp only [cells, List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with ((⟨index, _, rfl⟩ | ⟨index, _, rfl⟩) | ⟨index, _, rfl⟩) | rfl
  · exact PathGLoopProgram.registers_zero variant _
  · exact state_block_zero variant index
  · exact message_block_zero variant index
  · exact scratch_zero variant

/-- All65 initial native tokens are constructed from real zero reads:32GPRs,
16state words,16message words, and the separate scratch word. -/
theorem initialization (variant : Variant) :
    initialImage (before variant) cells = some (data variant).machine.initialMemory := by
  have allZero (domain : List Cell)
      (reads : ∀ cell ∈ domain, cell.read (before variant) = .ok 0 (before variant)) :
      initialImage (before variant) domain = some (domain.map old) := by
    induction domain with
    | nil => rfl
    | cons cell rest ih =>
      have next := ih (fun item member => reads item (List.mem_cons_of_mem cell member))
      simp only [initialImage] at next
      simp only [initialImage, List.mapM_cons, reads cell List.mem_cons_self, bind, Option.bind,
        next, List.map_cons, old]
      rfl
  exact allZero cells (cells_zero variant)

theorem cells_count : cells.length = 65 := by decide +kernel

theorem cells_distinct : (cells.map Cell.addressCode).Nodup := by decide +kernel

/-- Every public RAM cell is within the selected platform's physical RAM,
above the ROM split, without evaluating the whole symbolic RAM domain. -/
theorem ram_scope (address : BitVec 32) (member : Cell.ram address ∈ cells) :
    ROM.limit ≤ address.toNat ∧ address.toNat + 4 ≤ 2 ^ 30 := by
  simp only [cells, List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with ((⟨index, _, same⟩ | ⟨index, _, same⟩) | ⟨index, _, same⟩) | same
  · cases same
  · cases same
    fin_cases index <;> decide +kernel
  · cases same
    fin_cases index <;> decide +kernel
  · cases same
    decide +kernel

theorem cells_aligned (cell : Cell) (member : cell ∈ cells) : cell.Aligned := by
  simp only [cells, List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with ((⟨index, _, rfl⟩ | ⟨index, _, rfl⟩) | ⟨index, _, rfl⟩) | rfl
  · trivial
  · dsimp only [Cell.Aligned]
    fin_cases index <;> decide +kernel
  · dsimp only [Cell.Aligned]
    fin_cases index <;> decide +kernel
  · change scratchAddress.toNat % 4 = 0
    decide +kernel

/-- Concrete public input profile for each actual program variant. The initial
PC is0 and native clock is(4,0); the memory seeds have timestamp0. The56 actual
workers are all G workers, so the round-mask side condition is empty. -/
theorem inputs (variant : Variant) :
    UnifiedReduced.Caller.MixedMemoryInputs (data variant) (ordinaryProgram variant)
      (before variant) [128, 156] [0, 4, 8, 12, 16, 20, 132, 144, 148, 152] cells := by
  refine ⟨⟨caller_image variant, ?_, ?_⟩, ordinary_image variant, initialization variant,
    cells_distinct, cells_aligned, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · change (4 : Nat) % 4 = 0
    decide +kernel
  · intro worker member family
    change worker ∈ workerRows variant at member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    cases family

end Tests.PathGLoopNative
