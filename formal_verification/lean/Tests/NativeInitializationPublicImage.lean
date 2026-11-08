import Airbender.Review.Circuits.ReducedMachine.InitializationPublicImageTheorems
import Tests.NativeInitializationBatch

namespace Airbender.Tests.NativeInitializationPublicImage
open Airbender.NativeInitializationPublicImage
open Airbender.NativeInitializationBatch (Proof)
open Airbender.ReducedMachine.NativeInitialState (state)
open Airbender.ReducedMachine.NativeInitialStateProofs
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
open Airbender.Reference.RiscV.Sail (State)
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- These are symbolic original-Sail constructor controls, not nonempty native
    source/global/worker/physical witnesses or attack/defect certificates. -/
theorem original_pc_zero (before : State) :
    Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (state before) = .ok 0 (state before) := pc_read before

theorem original_x0_zero (before : State) :
    (Trace.Cell.register 0).read (state before) = .ok 0 (state before) := gpr_read before 0

theorem original_x31_zero (before : State) :
    (Trace.Cell.register 31).read (state before) = .ok 0 (state before) := gpr_read before 31

theorem original_all_gprs (before : State) (index : BitVec 5) :
    (Trace.Cell.register index).read (state before) = .ok 0 (state before) := gpr_read before index

theorem missing_pc_is_inserted (before : State) :
    ({before with regs := ∅} : State).regs.get? .PC = none ∧
    Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (state {before with regs := ∅}) =
      .ok 0 (state {before with regs := ∅}) := ⟨by simp,pc_read _⟩

theorem configuration_lookup_preserved (before : State) :
    (state before).regs.get? .mstatus = before.regs.get? .mstatus := register_frame before .mstatus (by decide +kernel)

theorem next_pc_lookup_preserved (before : State) :
    (state before).regs.get? .nextPC = before.regs.get? .nextPC := register_frame before .nextPC (by decide +kernel)

theorem first_ram_word (before : State) :
    (Trace.Cell.ram (BitVec.ofNat 32 4194304)).read (state before) = .ok 0 (state before) := ram_read before _ (by decide +kernel)

theorem unaligned_ram_word (before : State) :
    (Trace.Cell.ram (BitVec.ofNat 32 4194305)).read (state before) = .ok 0 (state before) := ram_read before _ (by decide +kernel)

theorem last_rv32_word (before : State) :
    (Trace.Cell.ram (BitVec.ofNat 32 4294967295)).read (state before) = .ok 0 (state before) := ram_read before _ (by decide +kernel)

theorem final_halo_byte (before : State) :
    (state before).mem[4294967298]? = some 0 := ram_byte before _ (by decide +kernel) (by decide +kernel)

theorem outside_halo_preserved (before : State) :
    (state before).mem[4294967299]? = before.mem[4294967299]? := outside_byte before _ (by decide +kernel)

theorem complete_native_rom (before : State) :
    Verification.wordROMImage (state before) 1048576 = some Airbender.ReducedMachine.NativeROM.complete := rom_image before

/-- Successful original ROM reads are distinct from native zero shadow values. -/
theorem rom_word_four (before : State) :
    (Trace.Cell.ram 16).read (state before) = .ok (BitVec.ofNat 32 21015) (state before) := by
  have read := rom_read before (4 : Fin 1048576)
  have value : Airbender.ReducedMachine.NativeROM.fixture.word 4 = BitVec.ofNat 32 21015 := by
    rw [Verification.WordROM.word, Airbender.ReducedMachine.NativeROMProofs.fixture_words]
    rfl
  change (Trace.Cell.ram 16).read (state before) = .ok (Airbender.ReducedMachine.NativeROM.fixture.word 4) (state before) at read
  rw [value] at read
  exact read

theorem zero_shadow_distinct_from_rom (before : State) :
    (Trace.Cell.ram 16).read (state before) ≠ .ok 0 (state before) := by
  rw [rom_word_four]
  intro same
  have values := (EStateM.Result.ok.inj same).1
  exact (by decide +kernel : (BitVec.ofNat 32 21015 : BitVec 32) ≠ 0) values

/-- Domain iteration preserves duplicate cells, rather than silently deduping. -/
theorem duplicate_image_cells (before : State) :
    Trace.initialImage (p := mersenne31Modulus) (state before) [Trace.Cell.register 0,Trace.Cell.register 0] =
      some [(Trace.Cell.register 0).initialToken 0,(Trace.Cell.register 0).initialToken 0] := by
  apply image_of_reads (state before)
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst c
  exact gpr_read before 0

theorem zero_boot_profile_derived (before : State) (cells : List Trace.Cell) :
    Trace.InitialProfile (state before) cells := initial_profile before cells

theorem complete_empty_image (before : State) : Effects ([] : List (Proof F)) before :=
  native_constructed_public_image _ _ _ _ _ _ Airbender.Tests.NativeInitializationBatch.empty_combined_component before

theorem complete_conditional_image {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (before : State) : Effects proofs before := native_constructed_public_image embed memory ch pc gamma config accepted before

theorem complete_conditional_memory {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    (imageTokens proofs ++ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch true).Perm
      (Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs ++ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false) :=
  native_constructed_memory_matching embed memory ch pc gamma config accepted

end Airbender.Tests.NativeInitializationPublicImage
