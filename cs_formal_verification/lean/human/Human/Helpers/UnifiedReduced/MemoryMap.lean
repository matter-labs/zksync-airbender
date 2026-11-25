module
public import Human.ISA.RV32

@[expose] public section
namespace RV

abbrev writableAt (romEnd : Nat) (a : Word) (n : Nat) := romEnd ≤ a.toNat ∧ a.toNat + n ≤ RAM_END
abbrev State.loadViewAt (s : State) (romEnd : Nat) (a : Word) := if a.toNat < romEnd then s.rom a else s.mem a

/-- Execute with the compiled machine's ROM boundary. The guest ISA is shared by both host fields. -/
abbrev execAt (romEnd : Nat) (s : State) : Instr → Option State
  | .load n signed rd rs1 off =>
    let a := s.getReg rs1 + off
    let x := read (s.loadViewAt romEnd) a n
    if rd = 0 then some s.nextInstr else if aligned a n ∧ readable a n then
      some (s.setReg rd (if signed then (x.setWidth (8*n)).signExtend 32 else x)).nextInstr else none
  | .store n rs2 rs1 off =>
    let a := s.getReg rs1 + off
    if aligned a n ∧ writableAt romEnd a n then some (s.store a (s.getReg rs2) n).nextInstr else none
  | i => exec s i

abbrev stepAt (romEnd : Nat) (s : State) : Option State :=
  if s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 ≤ romEnd then
    (decode (read s.rom s.pc 4)).bind (execAt romEnd s) else none

/-- Execute one instruction for each participating row. -/
def runAt (romEnd : Nat) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (runAt romEnd n s).bind (stepAt romEnd)

end RV
