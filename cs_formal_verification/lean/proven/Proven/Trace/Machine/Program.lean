module
public import Human.Helpers.Decoder.RVMachineProgram
public import Proven.Trace.RVFetch
public import Mathlib.Tactic.IntervalCases
public import Std.Data.TreeMap.Lemmas

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The address index has the same result as a search of the public entry list. -/
theorem machine_program_index_lookup (program : List RVMachineProgramEntry) (pc : Nat) :
    (rvMachineProgramIndex program)[pc]? = program.find? (fun entry => entry.pc.toNat == pc) := by
  induction program with
  | nil => simp [rvMachineProgramIndex]
  | cons entry program ih =>
    simp only [rvMachineProgramIndex, List.foldr_cons, Std.TreeMap.getElem?_insert,
      List.find?_cons]
    change (if compare entry.pc.toNat pc = .eq then some entry else
      (rvMachineProgramIndex program)[pc]?) = _
    rw [ih]
    cases beq : entry.pc.toNat == pc with
    | false =>
      have different : entry.pc.toNat ≠ pc := by
        intro equal
        rw [equal] at beq
        simp at beq
      simp [different]
    | true =>
      have equal : entry.pc.toNat = pc := by simpa only [beq_iff_eq] using beq
      simp [equal]

/-- A populated native slot retains an entry of the public program. -/
theorem machine_program_slot_member {program : List RVMachineProgramEntry} {index : Nat}
    {entry : RVMachineProgramEntry} (slot : rvMachineProgramSlot program index = some entry) :
    entry ∈ program := by
  exact List.mem_of_find?_eq_some (by
    simpa only [rvMachineProgramSlot, machine_program_index_lookup] using slot)

/-- Ordinary machine metadata preserves the complete existing nine-column query. -/
theorem ordinary_query {Kind : Type} (family : Kind → RVMachineDecoderFamily) (entry : RVProgramEntry Kind) :
    ((RVMachineDecoderData.ofOrdinary (family := family) entry.data).row entry.pc).map
      (fun (value : Nat) => (value : ZMod babyBearModulus)) = entry.query := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [RVMachineDecoderData.ofOrdinary, RVMachineDecoderData.row,
      RVProgramEntry.query, Arithmetic.Word.ofBitVec, Arithmetic.limbBase]

/-- A public machine entry is an aligned ROM word with its actual RV instruction and native metadata. -/
theorem machine_entry_fetch {config : RVMachineConfig} {initial : RV.State}
    {addresses : List (BitVec 32)} {program : List RVMachineProgramEntry}
    (image : rvMachineProgramImage config initial addresses = some program)
    (entry : RVMachineProgramEntry) (present : entry ∈ program) :
    (entry.pc.toNat < RV.ROM_END ∧ entry.pc.toNat % 4 = 0) ∧
      entry.bits = RV.read initial.rom entry.pc 4 ∧
      ∃ instruction, RV.decode entry.bits = some instruction ∧
        rvMachineDecoderFields config instruction = some entry.data := by
  simp only [rvMachineProgramImage, Option.some.injEq] at image
  subst program
  obtain ⟨pc, _, built⟩ := List.mem_filterMap.mp present
  unfold rvMachineProgramEntryWith at built
  split at built
  · cases built
  rename_i admitted
  have guard : pc.toNat < RV.ROM_END ∧ pc.toNat % 4 = 0 := by simpa only [rvProgramFetchAllowed, not_not] using admitted
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
