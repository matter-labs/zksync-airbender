import Human.Call
import Human.Spec
import Human.SpecPoly
import Image

/-! # The final theorem (statement only)

The proof is `RV.program_correct` in `slop/Slop/RV/Final.lean`; `verify.sh` checks that it proves exactly
`RV.ProgramCorrect` and uses only Lean's standard axioms. -/

namespace RV

/-- The flat binary `build/app.bin` (= `Image.bytes`) is in memory from address 0. -/
def ImageLoaded (s : State) : Prop :=
  ∀ i (h : i < Image.bytes.size), s.mem (BitVec.ofNat 32 i) = Image.bytes[i]

/-- Started at address 0 (registers arbitrary) with the image loaded and a field element `x` (`x ≤ P`) at
`INPUT`, the program reaches `_halt` with `a0 = combine x` and `a1 = poly x` in the Mersenne31 field (as a
`u32 ≤ P`, Airbender's representation), and stays there: any number of further steps keeps the PC at
`_halt` and every register unchanged (Airbender reads the outputs some steps later). -/
def ProgramCorrect : Prop :=
  ∀ (s : State) (x : Word), s.pc = 0 → ImageLoaded s → read s.mem (BitVec.ofNat 32 Image.INPUT) 4 = x →
    x.toNat ≤ Spec.P →
    ∃ n s', run n s = some s' ∧ s'.pc = BitVec.ofNat 32 Image.halt ∧
      s'.getReg 10 = Spec.combine x ∧
      (s'.getReg 11).toNat ≤ Spec.P ∧ ((s'.getReg 11).toNat : ZMod Spec.P) = Spec.poly (x.toNat : ZMod Spec.P) ∧
      ∀ k, ∃ s'', run k s' = some s'' ∧ s''.pc = s'.pc ∧ ∀ i, s''.getReg i = s'.getReg i

end RV
