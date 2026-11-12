module
public import Proven.Trace.Machine.ModularData
public import Proven.AddSub.Modular.RVArithmetic
public import Proven.Arithmetic.Word

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic
set_option warningAsError true

/-- The modular calculation reads original register words from the row's pre-state. -/
def modularInput (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5) (before : RV.State) : AddSub.Modular.Input :=
  ⟨opcode, before.getReg rs1, before.getReg rs2, before.getReg rd, rs1, rs2, rd, Word.ofBitVec before.pc, before⟩

/-- A bounded native word and its RV read have the same field residue. -/
theorem modular_word_residue {w : Nat → ZMod babyBearModulus} {lo hi : Nat} {value : BitVec 32}
    (bound : (Word.mk (w lo).val (w hi).val).Bounded)
    (read : value = (Word.mk (w lo).val (w hi).val).toBitVec) :
    w lo + 65536 * w hi = (value.toNat : ZMod babyBearModulus) := by
  rw [read, Word.toBitVec_toNat bound]
  simp [Word.value, limbBase]

end Airbender.Trace.Machine.Proofs
