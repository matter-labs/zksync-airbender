import Human.Helpers.Decoder.RVProgram

/-! Fetch link for the RV program table (piece D). A public entry of `rvProgramImageWith` is an aligned ROM word
    that `RV.decode` reads from the starting ROM image; its native data is `projection` of the decoded instruction.
    Structural unpacking only. -/

namespace Airbender.Trace
open Arithmetic

/-- Unpack one successful `rvProgramEntryWith`: the guard, the public bytes, the decoded instruction and its data. -/
theorem rvProgramEntryWith_some {Kind : Type}
    {projection : RV.Instr → Option (DecoderData Kind)}
    {before : RV.State} {pc : BitVec 32} {entry : RVProgramEntry Kind}
    (h : rvProgramEntryWith projection before pc = some entry) :
    entry.pc = pc ∧ (pc.toNat < RV.ROM_END ∧ pc.toNat % 4 = 0) ∧
      entry.bits = RV.read before.rom pc 4 ∧
      ∃ i, RV.decode entry.bits = some i ∧ projection i = some entry.data := by
  unfold rvProgramEntryWith at h
  split at h
  · cases h
  rename_i hg
  have guard : pc.toNat < RV.ROM_END ∧ pc.toNat % 4 = 0 := by
    simpa using hg
  dsimp only at h
  cases hd : RV.decode (RV.read before.rom pc 4) with
  | none => simp [hd] at h
  | some i =>
    cases hp : projection i with
    | none => simp [hd, hp] at h
    | some data =>
      simp only [hd, hp, bind, Option.bind, pure, Option.some.injEq] at h
      subst h
      exact ⟨rfl, guard, rfl, i, hd, hp⟩

/-- Every entry of a successful public image was built at one of the listed addresses. -/
theorem mem_rvProgramImage {Kind : Type}
    {projection : RV.Instr → Option (DecoderData Kind)} {before : RV.State} :
    ∀ {addresses : List (BitVec 32)} {program : List (RVProgramEntry Kind)},
      rvProgramImageWith projection before addresses = some program →
      ∀ entry ∈ program, ∃ pc ∈ addresses, rvProgramEntryWith projection before pc = some entry
  | [], program, image, entry, present => by
    unfold rvProgramImageWith at image
    simp only [List.mapM_nil, pure, Option.some.injEq] at image
    subst image
    simp at present
  | address :: addresses, program, image, entry, present => by
    unfold rvProgramImageWith at image
    rw [List.mapM_cons] at image
    cases first : rvProgramEntryWith projection before address with
    | none => simp [first, bind, Option.bind] at image
    | some head =>
      cases rest : addresses.mapM (rvProgramEntryWith projection before) with
      | none => simp [first, rest, bind, Option.bind] at image
      | some entries =>
        simp only [first, rest, bind, Option.bind, pure, Option.some.injEq] at image
        subst image
        rcases List.mem_cons.mp present with rfl | present
        · exact ⟨address, by simp, first⟩
        · obtain ⟨pc, mem, h⟩ := mem_rvProgramImage rest entry present
          exact ⟨pc, by simp [mem], h⟩

/-- Fetch link for a program entry: its PC is an aligned ROM address, its bytes are the ROM image's bytes at
    that address, and they decode (`RV.decode`) to an instruction whose native data (`projection`) is the entry's. -/
theorem rvProgram_entry_fetch {Kind : Type}
    {projection : RV.Instr → Option (DecoderData Kind)} {initial : RV.State}
    {addresses : List (BitVec 32)} {program : List (RVProgramEntry Kind)}
    (image : rvProgramImageWith projection initial addresses = some program)
    (entry : RVProgramEntry Kind) (present : entry ∈ program) :
    (entry.pc.toNat < RV.ROM_END ∧ entry.pc.toNat % 4 = 0) ∧
      entry.bits = RV.read initial.rom entry.pc 4 ∧
      ∃ i, RV.decode entry.bits = some i ∧ projection i = some entry.data := by
  obtain ⟨pc, _, built⟩ := mem_rvProgramImage image entry present
  obtain ⟨pcEq, guard, bits, i, decoded, data⟩ := rvProgramEntryWith_some built
  subst pcEq
  exact ⟨guard, bits, i, decoded, data⟩

/-- If the pre-state's ROM image is the starting one and its PC is the entry's PC, `RV.step` executes the entry's
    decoded instruction, and the fetched word is the public entry's bytes. -/
theorem rv_step_fetch (s initial : RV.State) (agree : s.rom = initial.rom)
    (pc : BitVec 32) (hpc : s.pc = pc) (guard : pc.toNat < RV.ROM_END ∧ pc.toNat % 4 = 0) :
    RV.read s.rom s.pc 4 = RV.read initial.rom pc 4 ∧
      RV.step s = (RV.decode (RV.read initial.rom pc 4)).bind (RV.exec s) := by
  subst hpc
  have word : RV.read s.rom s.pc 4 = RV.read initial.rom s.pc 4 := by rw [agree]
  refine ⟨word, ?_⟩
  unfold RV.step
  have bound : s.pc.toNat + 4 ≤ RV.ROM_END := by
    unfold RV.ROM_END at guard ⊢
    omega
  rw [if_pos ⟨guard.2, bound⟩, word]

end Airbender.Trace
