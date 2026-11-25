module
public import Human.Helpers.UnifiedReduced.MemoryMap
public import Proven.ISA.RV.Mem
public import Proven.ISA.RV.Step
public import Human.Helpers.Core.Word

@[expose] public section
namespace RV

theorem execAt_default (s : State) (i : Instr) : execAt ROM_END s i = exec s i := by
  cases i <;> rfl

theorem stepAt_default (s : State) : stepAt ROM_END s = step s := by
  simp only [stepAt, step, funext (execAt_default s)]

theorem runAt_default (n : Nat) (s : State) : runAt ROM_END n s = run n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runAt, ih, run_add n 1]
    cases run n s with
    | none => rfl
    | some t => simp [stepAt_default, run]

theorem read_loadViewAt_ram {romEnd : Nat} (s : State) (a : Word) (n : Nat) (lo : romEnd ≤ a.toNat)
    (hi : a.toNat + n ≤ 2 ^ 32) : read (s.loadViewAt romEnd) a n = read s.mem a n := by
  apply read_congr
  intro k hk
  apply ite_eq_right
  bv_omega

theorem read_loadViewAt_rom {romEnd : Nat} (s : State) (a : Word) (n : Nat) (h : a.toNat + n ≤ romEnd) :
    read (s.loadViewAt romEnd) a n = read s.rom a n := by
  apply read_congr
  intro k hk
  apply ite_eq_left
  bv_omega

theorem writableAt_index {limbs : Nat} (a : Word) (h : limbs ≤ (Airbender.Arithmetic.Word.ofBitVec a).hi) :
    limbs * 65536 ≤ a.toNat := by
  dsimp [Airbender.Arithmetic.Word.ofBitVec, Airbender.Arithmetic.limbBase] at h
  omega

theorem execAt_load {romEnd : Nat} (s : State) n sg rd rs1 off (hrd : rd ≠ 0) (ha : aligned (s.getReg rs1 + off) n)
    (hr : readable (s.getReg rs1 + off) n) :
    execAt romEnd s (.load n sg rd rs1 off) = some (s.setReg rd
      (if sg then ((read (s.loadViewAt romEnd) (s.getReg rs1 + off) n).setWidth (8*n)).signExtend 32
        else read (s.loadViewAt romEnd) (s.getReg rs1 + off) n)).nextInstr := by
  simp only [execAt, hrd, ↓reduceIte]
  exact ite_eq_left ⟨ha, hr⟩

theorem execAt_store {romEnd : Nat} (s : State) n rs2 rs1 off (ha : aligned (s.getReg rs1 + off) n)
    (hw : writableAt romEnd (s.getReg rs1 + off) n) :
    execAt romEnd s (.store n rs2 rs1 off) = some (s.store (s.getReg rs1 + off) (s.getReg rs2) n).nextInstr :=
  ite_eq_left ⟨ha, hw⟩

end RV
