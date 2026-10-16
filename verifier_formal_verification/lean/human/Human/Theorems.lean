import Human.Call
import Human.Spec
import Human.SpecPoly
import Human.SpecExt4
import Image
import ImageMop
import Human.SpecBlake
import Human.SpecFS

/-! # The final theorems (statements only)

The proofs are `RV.program_correct` and `RV.program_correct_mop` in `slop/Slop/RV/FinalPlain.lean` and
`slop/Slop/RV/FinalMop.lean`; `verify.sh` checks that they prove exactly `RV.ProgramCorrect` and
`RV.ProgramCorrectMop` and use only Lean's standard axioms. -/

namespace RV
open ABI

/-- A flat binary (such as `build/app.bin` = `Image.bytes`: the code, then the `.rodata` load image) is in memory
from address 0. -/
def ImageLoaded (bytes : Array (BitVec 8)) (s : State) : Prop :=
  ∀ i (h : i < bytes.size), s.mem (BitVec.ofNat 32 i) = bytes[i]

/-- RAM is zero, as Airbender guarantees at start. -/
def RamZero (s : State) : Prop := ∀ addr : Word, ROM_END ≤ addr.toNat → addr.toNat < RAM_END → s.mem addr = 0

/-- A register value as a BabyBear element. -/
def bb (w : Word) : Spec.F := w.toNat

/-- Booted at address 0 (registers arbitrary) with the image loaded and RAM zero, the input (CSR `0x7c0`) starting
with a Mersenne31 element `x` (`x ≤ P`), a BabyBear Ext4 element `y` (4 canonical limbs, `< BabyBearP`), and the
prover's Fiat–Shamir claim `v` (4 words, `Human/SpecFS.lean`): if the claim is right, the program reaches its final
self-jump `halt` with
* `a0 = combine x`, `a1 = poly x` in the Mersenne31 field (as a `u32 ≤ P`, Airbender's representation),
* `a2 … a5` (`x12 … x15`) the limbs of `poly4 y` in BabyBear's Ext4 (canonical),
* `a6, a7` (`x16, x17`) the first two words of the Blake2s (7 rounds) digest of the five input words,
* the other output registers `x18 … x25` zero (riscv_common's 16-word output convention),
and stays there: any number of further steps keeps the PC at `halt` and every register unchanged (Airbender reads
the outputs some steps later); if the claim is wrong, no run ever reaches `halt` (the program fails: Airbender cannot
prove it). For the image `bytes` with its final self-jump at `halt`. -/
def ProgramCorrectOf (bytes : Array (BitVec 8)) (halt : Nat) : Prop :=
  ∀ (start : State) (x y0 y1 y2 y3 v0 v1 v2 v3 : Word) (rest : List Word), start.pc = 0 →
    ImageLoaded bytes start → RamZero start →
    start.input = x :: y0 :: y1 :: y2 :: y3 :: v0 :: v1 :: v2 :: v3 :: rest → x.toNat ≤ Spec.P →
    y0.toNat < BabyBearP → y1.toNat < BabyBearP → y2.toNat < BabyBearP → y3.toNat < BabyBearP →
    (Spec.claimOK #v[x, y0, y1, y2, y3] #v[v0, v1, v2, v3] →
    ∃ numSteps final, run numSteps start = some final ∧ final.pc = BitVec.ofNat 32 halt ∧
      final.getReg a0 = Spec.combine x ∧
      (final.getReg a1).toNat ≤ Spec.P ∧
      ((final.getReg a1).toNat : ZMod Spec.P) = Spec.poly (x.toNat : ZMod Spec.P) ∧
      (∀ i : Reg, 12 ≤ i.toNat → i.toNat ≤ 15 → (final.getReg i).toNat < BabyBearP) ∧
      Spec.ofLimbs (bb (final.getReg 12)) (bb (final.getReg 13)) (bb (final.getReg 14)) (bb (final.getReg 15)) =
        Spec.poly4 (Spec.ofLimbs (bb y0) (bb y1) (bb y2) (bb y3)) ∧
      final.getReg 16 = (Spec.blake5 #v[x, y0, y1, y2, y3])[0] ∧
      final.getReg 17 = (Spec.blake5 #v[x, y0, y1, y2, y3])[1] ∧
      (∀ i : Reg, 18 ≤ i.toNat → i.toNat ≤ 25 → final.getReg i = 0) ∧
      ∀ moreSteps, ∃ later, run moreSteps final = some later ∧ later.pc = final.pc ∧
        ∀ i, later.getReg i = final.getReg i) ∧
    (¬ Spec.claimOK #v[x, y0, y1, y2, y3] #v[v0, v1, v2, v3] →
      ∀ numSteps final, run numSteps start = some final → final.pc ≠ BitVec.ofNat 32 halt)

/-- The final theorem for the plain-Rust image (`build/app.bin`, `lean/image/Image.lean`). -/
def ProgramCorrect : Prop := ProgramCorrectOf Image.bytes Image.halt

/-- The final theorem for the field-opcode image (`build/app_mop.bin`, `lean/image/ImageMop.lean`). -/
def ProgramCorrectMop : Prop := ProgramCorrectOf ImageMop.bytes ImageMop.halt

end RV
