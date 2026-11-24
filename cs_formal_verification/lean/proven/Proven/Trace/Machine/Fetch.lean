module
public import Proven.Trace.Machine.Program
public import Proven.Trace.RVProgram

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The machine query binds both canonical PC limbs through the public ROM address. -/
theorem machine_native_query_pc_word {p : Nat} (hp : limbBase < p)
    {columns : TraceColumns} {decoder : DecoderColumns} {w : Nat → ZMod p} {entry : RVMachineProgramEntry}
    (query : nativeDecoderQuery columns decoder w =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod p))) :
    (Word.mk (w columns.initialPC[0]).val (w columns.initialPC[1]).val) = Word.ofBitVec entry.pc := by
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[0]) query
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[1]) query
  simp only [RVMachineDecoderData.row, Vector.getElem_map] at low high
  change w columns.initialPC[0] = ((Word.ofBitVec entry.pc).lo : ZMod p) at low
  change w columns.initialPC[1] = ((Word.ofBitVec entry.pc).hi : ZMod p) at high
  exact word_of_pc_query hp low high

/-- Every family starts at the public PC of its native machine entry. -/
theorem machine_query_pc {Kind : Type} [CircuitLayout Kind] {p : Nat} (hp : limbBase < p)
    {row : Row p Kind} {entry : RVMachineProgramEntry}
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod p))) :
    row.start.word.toBitVec = entry.pc := by
  have word : row.start.word = Word.ofBitVec entry.pc := machine_native_query_pc_word hp query
  rw [word, Word.ofBitVec_roundtrip]

/-- A reachable state with the public ROM and entry PC fetches the entry's actual RV instruction. -/
theorem machine_current_fetch {config : RVMachineConfig} {initial before : RV.State}
    {addresses : List (BitVec 32)} {program : List RVMachineProgramEntry}
    (image : rvMachineProgramImage config initial addresses = some program)
    {entry : RVMachineProgramEntry} (present : entry ∈ program)
    (rom : before.rom = initial.rom) (pc : before.pc = entry.pc) :
    ∃ instruction, RV.decode entry.bits = some instruction ∧
      rvMachineDecoderFields config instruction = some entry.data ∧ RV.step before = RV.exec before instruction := by
  obtain ⟨guard, bits, instruction, decoded, fields⟩ := machine_entry_fetch image entry present
  have fetch := (rv_step_fetch before initial rom entry.pc pc guard).2
  rw [← bits, decoded, Option.bind_some] at fetch
  exact ⟨instruction, decoded, fields, fetch⟩

end Airbender.Trace.Machine.Proofs
