import Human.Call
import Human.Spec
import Human.SpecPoly
import Image

/-! # The final theorem (statement only)

The proof is `RV.program_correct` in `slop/Slop/RV/Final.lean`; `verify.sh` checks that it proves exactly
`RV.ProgramCorrect` and uses only Lean's standard axioms. -/

namespace RV
open ABI

/-- The flat binary `build/app.bin` (= `Image.bytes`) is in memory from address 0. -/
def ImageLoaded (s : State) : Prop :=
  ∀ i (h : i < Image.bytes.size), s.mem (BitVec.ofNat 32 i) = Image.bytes[i]

/-- Started at address 0 (registers arbitrary) with the image loaded and a field element `x` (`x ≤ P`) at
`INPUT`, the program reaches `_halt` with `a0 = combine x` and `a1 = poly x` in the Mersenne31 field (as a
`u32 ≤ P`, Airbender's representation), and stays there: any number of further steps keeps the PC at
`_halt` and every register unchanged (Airbender reads the outputs some steps later). -/
def ProgramCorrect : Prop :=
  ∀ (start : State) (x : Word), start.pc = 0 → ImageLoaded start →
    read start.mem (BitVec.ofNat 32 Image.INPUT) 4 = x → x.toNat ≤ Spec.P →
    ∃ numSteps final, run numSteps start = some final ∧ final.pc = BitVec.ofNat 32 Image.halt ∧
      final.getReg a0 = Spec.combine x ∧
      (final.getReg a1).toNat ≤ Spec.P ∧
      ((final.getReg a1).toNat : ZMod Spec.P) = Spec.poly (x.toNat : ZMod Spec.P) ∧
      ∀ moreSteps, ∃ later, run moreSteps final = some later ∧ later.pc = final.pc ∧
        ∀ i, later.getReg i = final.getReg i

end RV
