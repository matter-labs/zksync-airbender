import HumanSail.Airbender
import Human.Theorems

/-! # What ties our fast spec to Sail (statements only)

Two facts make our own spec `RV.step` (`Human/RV32.lean`) trustworthy without reviewing it line by line:
1. `decode_is_sail`: for every word in our encoding table, Sail's own decoder gives the same instruction, except
   for the extra encodings Airbender accepts (`ExtraEncoding`).
2. `step_is_airbender`: our step does exactly what the Airbender machine (`HumanSail/Airbender.lean`: Sail's
   `execute` plus the listed changes) does, on everything a program can see.
With 2, the final theorem holds on the Airbender machine itself: 3. `ProgramCorrect`.
Proofs (checked by `verify.sh` when the Sail model is generated): `Slop.Equiv.decode_is_sail`
(`slop/Slop/Equiv/Decode.lean`), `Slop.Equiv.step_is_airbender` (`slop/Slop/Equiv/StepIsAirbender.lean`),
`Slop.Equiv.program_correct_airbender` (`slop/Slop/Equiv/Final.lean`). -/

open Sail SailRV32 SailRV32.Functions Human RV.ABI

namespace Airbender

/-- Register `i` of a Sail state, read the way Sail's instructions read it (x0 reads as 0). -/
noncomputable def getReg (σ : SailState) (i : RV.Reg) : BitVec 32 :=
  match runSail (rX_bits (.Regidx i)) σ with | .ok v _ => v | .error _ _ => 0

/-- Our state `s` and Sail's state `σ` agree on everything a program can see: PC, registers, memory. -/
def Agree (s : RV.State) (σ : SailState) : Prop :=
  Configured σ ∧ σ.regs .PC = s.pc ∧ (∀ i, getReg σ i = s.getReg i) ∧
  (∀ addr : RV.Word, σ.mem addr.toNat = s.mem addr)

/-- Encodings Airbender accepts beyond standard RV32IM (`-- Airbender:` rows of `RV.decode`): JALR with
funct3 ≠ 0; SLT, SLTU, XOR, OR, AND with funct7 other than 0000000 (and 0000001, which is the M extension). -/
def ExtraEncoding (word : RV.Word) : Prop :=
  let opcode := word.extractLsb' 0 7; let funct3 := word.extractLsb' 12 3; let funct7 := word.extractLsb' 25 7
  (opcode = 0b1100111 ∧ funct3 ≠ 0) ∨
  (opcode = 0b0110011 ∧ funct3 ∈ [2, 3, 4, 6, 7] ∧ funct7 ≠ 0 ∧ funct7 ≠ 1)

/-- 1. Sail decodes every standard word of our table to the same instruction (on any Airbender state). -/
def DecodeIsSail : Prop :=
  ∀ word instr σ, RV.decode word = some instr → ¬ ExtraEncoding word → Configured σ →
    runSail (ext_decode word) σ = .ok (toSail instr) σ

/-- 2. One step of our spec is one step of the Airbender machine. -/
def StepIsAirbender : Prop :=
  ∀ s s' σ, Agree s σ → RV.step s = some s' → ∃ σ', step σ = some σ' ∧ Agree s' σ'

/-- `numSteps` steps of the Airbender machine. -/
noncomputable def run : (numSteps : Nat) → SailState → Option SailState
  | 0,     σ => some σ
  | n + 1, σ => (step σ).bind (run n)

/-- 3. The final theorem on the Airbender machine itself: `RV.ProgramCorrect` (`Human/Theorems.lean`), with Sail's
state in place of ours. Started from any Airbender state (`Configured`: privilege, CSRs, memory map as after reset) at
address 0, with the image loaded, RAM zero except a field element `x` at `INPUT`, Airbender reaches `halt` with
`a0 = combine x`, `a1 = poly x`, `x12 … x25` zero, and stays there. Follows from 1 and 2 and `RV.program_correct`. -/
def ProgramCorrectOf (bytes : Array (BitVec 8)) (INPUT halt : Nat) : Prop :=
  ∀ (start : SailState) (x : RV.Word), Configured start → start.regs .PC = 0 →
    (∀ i (h : i < bytes.size), start.mem i = bytes[i]) →
    (∀ addr : Nat, RV.ROM_END ≤ addr → addr < RV.RAM_END → (addr < INPUT ∨ INPUT + 4 ≤ addr) →
      start.mem addr = 0) →
    readBytes start.mem INPUT 4 = x → x.toNat ≤ Spec.P →
    ∃ numSteps final, run numSteps start = some final ∧ final.regs .PC = BitVec.ofNat 32 halt ∧
      getReg final a0 = Spec.combine x ∧
      (getReg final a1).toNat ≤ Spec.P ∧
      ((getReg final a1).toNat : ZMod Spec.P) = Spec.poly (x.toNat : ZMod Spec.P) ∧
      (∀ i : RV.Reg, 12 ≤ i.toNat → i.toNat ≤ 25 → getReg final i = 0) ∧
      ∀ moreSteps, ∃ later, run moreSteps final = some later ∧ later.regs .PC = final.regs .PC ∧
        ∀ i, getReg later i = getReg final i

/-- 3. for the image built by `rust/build.sh`. -/
def ProgramCorrect : Prop := ProgramCorrectOf Image.bytes Image.INPUT Image.halt

end Airbender
