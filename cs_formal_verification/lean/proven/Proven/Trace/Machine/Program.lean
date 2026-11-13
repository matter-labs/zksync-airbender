module
public import Human.Helpers.Decoder.RVMachineProgram
public import Proven.Trace.RVFetch
public import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Ordinary machine metadata preserves the complete existing nine-column query. -/
theorem ordinary_query {Kind : Type} (family : Kind → RVMachineDecoderFamily) (entry : RVProgramEntry Kind) :
    ((RVMachineDecoderData.ofOrdinary (family := family) entry.data).row entry.pc).map
      (fun (value : Nat) => (value : ZMod babyBearModulus)) = entry.query := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [RVMachineDecoderData.ofOrdinary, RVMachineDecoderData.row,
      RVProgramEntry.query, Arithmetic.Word.ofBitVec, Arithmetic.limbBase]

/-- A successful optional list traversal retains a source for each output occurrence. -/
theorem option_mapM_member {α β : Type} (build : α → Option β) :
    ∀ {inputs : List α} {outputs : List β}, inputs.mapM build = some outputs →
      ∀ output ∈ outputs, ∃ input ∈ inputs, build input = some output
  | [], outputs, image, output, present => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at image
    subst image
    simp at present
  | input :: inputs, outputs, image, output, present => by
    rw [List.mapM_cons] at image
    cases first : build input with
    | none => simp [first, bind, Option.bind] at image
    | some head =>
      cases rest : inputs.mapM build with
      | none => simp [first, rest, bind, Option.bind] at image
      | some tail =>
        simp only [first, rest, bind, Option.bind, pure, Option.some.injEq] at image
        subst image
        rcases List.mem_cons.mp present with rfl | present
        · exact ⟨input, List.mem_cons_self, first⟩
        · obtain ⟨source, member, built⟩ := option_mapM_member build rest output present
          exact ⟨source, List.mem_cons_of_mem input member, built⟩

/-- A public machine entry is an aligned ROM word with its actual RV instruction and native metadata. -/
theorem machine_entry_fetch {config : RVMachineConfig} {initial : RV.State}
    {addresses : List (BitVec 32)} {program : List RVMachineProgramEntry}
    (image : rvMachineProgramImage config initial addresses = some program)
    (entry : RVMachineProgramEntry) (present : entry ∈ program) :
    (entry.pc.toNat < RV.ROM_END ∧ entry.pc.toNat % 4 = 0) ∧
      entry.bits = RV.read initial.rom entry.pc 4 ∧
      ∃ instruction, RV.decode entry.bits = some instruction ∧
        rvMachineDecoderFields config instruction = some entry.data := by
  let build := fun pc : BitVec 32 => do
    if ¬(pc.toNat < RV.ROM_END ∧ pc.toNat % 4 = 0) then none else
      let bits := RV.read initial.rom pc 4
      let instruction ← RV.decode bits
      let data ← rvMachineDecoderFields config instruction
      pure (⟨pc, bits, data⟩ : RVMachineProgramEntry)
  change addresses.mapM build = some program at image
  obtain ⟨pc, _, built⟩ := option_mapM_member build image entry present
  dsimp only [build] at built
  split at built
  · cases built
  rename_i admitted
  have guard : pc.toNat < RV.ROM_END ∧ pc.toNat % 4 = 0 := by simpa using admitted
  cases decoded : RV.decode (RV.read initial.rom pc 4) with
  | none => simp [decoded] at built
  | some instruction =>
    cases fields : rvMachineDecoderFields config instruction with
    | none => simp [decoded, fields] at built
    | some data =>
      simp only [decoded, fields, bind, Option.bind, pure, Option.some.injEq] at built
      subst built
      exact ⟨guard, rfl, instruction, decoded, fields⟩

end Airbender.Trace.Machine.Proofs
