module
public import Proven.Trace.Machine.Program
public import Human.Circuits.AddSub.Modular.Model
public import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic
set_option warningAsError true

/-- Native arithmetic metadata for a nonzero modular destination. -/
def modularData (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5) : DecoderData :=
  ⟨.addSub, rs1, rs2, rd, ⟨0, 0⟩, 2 ^ (opcode.selector - 10), 0⟩

/-- The modular opcode selects one of the four existing native arithmetic bits. -/
theorem modular_mask_bound (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5) :
    (modularData opcode rs1 rs2 rd).mask < 512 := by
  cases opcode <;> norm_num [modularData, AddSub.Modular.Opcode.selector]

/-- The native modular mask has exactly its opcode bit. -/
theorem modular_mask_bit (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5)
    (k : Nat) (lower : 10 ≤ k) (upper : k ≤ 18) :
    (modularData opcode rs1 rs2 rd).mask.testBit (k - 10) = decide (k = opcode.selector) := by
  cases opcode <;> interval_cases k <;>
    dsimp only [modularData, AddSub.Modular.Opcode.selector] <;> decide

/-- Public machine preprocessing retains all modular register fields when rd is nonzero. -/
theorem machine_modular_fields (config : RVMachineConfig) (opcode : AddSub.Modular.Opcode)
    (rs1 rs2 rd : BitVec 5) (nonzero : rd ≠ 0) :
    rvMachineExtraFields config (.mop opcode.rvOp rd rs1 rs2) =
      some (RVMachineDecoderData.ofOrdinary (family := fun _ => config.arithmeticFamily)
        (modularData opcode rs1 rs2 rd)) := by
  cases opcode <;> simp only [rvMachineExtraFields, AddSub.Modular.Opcode.rvOp, ite_eq_right nonzero,
    rvModularMask, Option.map_some, modularData, AddSub.Modular.Opcode.selector, RVMachineDecoderData.ofOrdinary]
  all_goals rfl

end Airbender.Trace.Machine.Proofs
