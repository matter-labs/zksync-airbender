import HumanSail.Airbender
import Human.Theorems

/-! # What ties our fast spec to Sail (statements only)

Two facts make our own spec `RV.step` (`Human/RV32.lean`) trustworthy without reviewing it line by line:
1. `decode_is_sail`: for every word in our encoding table, Sail's own decoder gives the same instruction, except
   for the extra encodings Airbender accepts (`Lenient`).
2. `step_is_airbender`: our step does exactly what the Airbender machine (`HumanSail/Airbender.lean`: Sail's
   `execute` plus the listed changes) does, on everything a program can see.
With 2, the final theorem holds on the Airbender machine itself: 3. `ProgramCorrect`.
Proofs (checked by `verify.sh` when the Sail model is generated): `Slop.Equiv.decode_is_sail`
(`slop/Slop/Equiv/Decode.lean`), `Slop.Equiv.step_is_airbender` (`slop/Slop/Equiv/StepIsAirbender.lean`),
`Slop.Equiv.program_correct_airbender` (`slop/Slop/Equiv/Final.lean`). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Airbender

/-- Register `i` of a Sail state, read the way Sail's instructions read it (x0 reads as 0). -/
noncomputable def reg (σ : FState) (i : RV.Reg) : BitVec 32 :=
  match runF (rX_bits (.Regidx i)) σ with | .ok v _ => v | .error _ _ => 0

/-- Our state `s` and Sail's state `σ` agree on everything a program can see: PC, registers, memory. -/
def Agree (s : RV.State) (σ : FState) : Prop :=
  Sys σ ∧ σ.regs .PC = s.pc ∧ (∀ i, reg σ i = s.r i) ∧ (∀ a : RV.Word, σ.mem a.toNat = s.mem a)

/-- Encodings Airbender accepts beyond standard RV32IM (`-- Airbender:` rows of `RV.decode`): JALR with
funct3 ≠ 0; SLT, SLTU, XOR, OR, AND with funct7 other than 0000000 (and 0000001, which is the M extension). -/
def Lenient (w : RV.Word) : Prop :=
  let opcode := w.extractLsb' 0 7; let funct3 := w.extractLsb' 12 3; let funct7 := w.extractLsb' 25 7
  (opcode = 0b1100111 ∧ funct3 ≠ 0) ∨
  (opcode = 0b0110011 ∧ funct3 ∈ [2, 3, 4, 6, 7] ∧ funct7 ≠ 0 ∧ funct7 ≠ 1)

/-- 1. Sail decodes every standard word of our table to the same instruction (on any Airbender state). -/
def DecodeIsSail : Prop :=
  ∀ w i σ, RV.decode w = some i → ¬ Lenient w → Sys σ → runF (ext_decode w) σ = .ok (toSail i) σ

/-- 2. One step of our spec is one step of the Airbender machine. -/
def StepIsAirbender : Prop :=
  ∀ s t σ, Agree s σ → RV.step s = some t → ∃ σ', step σ = some σ' ∧ Agree t σ'

/-- `n` steps of the Airbender machine. -/
noncomputable def run : Nat → FState → Option FState
  | 0,     σ => some σ
  | n + 1, σ => (step σ).bind (run n)

/-- 3. The final theorem on the Airbender machine itself: `RV.ProgramCorrect` (`Human/Theorems.lean`), with Sail's
state in place of ours. Started from any Airbender state (`Sys`: privilege, CSRs, memory map as after reset) at
address 0, with the image loaded and a field element `x` at `INPUT`, Airbender reaches `_halt` with
`a0 = combine x`, `a1 = poly x` and stays there. Follows from 1 and 2 and `RV.program_correct`. -/
def ProgramCorrect : Prop :=
  ∀ (σ : FState) (x : RV.Word), Sys σ → σ.regs .PC = 0 →
    (∀ i (h : i < Image.bytes.size), σ.mem i = Image.bytes[i]) → readBytes σ.mem Image.INPUT 4 = x →
    x.toNat ≤ Spec.P →
    ∃ n σ', run n σ = some σ' ∧ σ'.regs .PC = BitVec.ofNat 32 Image.halt ∧
      reg σ' 10 = Spec.combine x ∧
      (reg σ' 11).toNat ≤ Spec.P ∧ ((reg σ' 11).toNat : ZMod Spec.P) = Spec.poly (x.toNat : ZMod Spec.P) ∧
      ∀ k, ∃ σ'', run k σ' = some σ'' ∧ σ''.regs .PC = σ'.regs .PC ∧ ∀ i, reg σ'' i = reg σ' i

end Airbender
