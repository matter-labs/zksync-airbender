module
public import Human.ISA.DelegationRuns

@[expose] public section

/-! The assumptions of the delegation-run claims can be met (`Human/ISA/DelegationRuns.lean`): concrete states whose
registers and buffers have the layout each run expects. -/

namespace RV.Deleg.NonVacuous
open Spec

/-- A state whose registers x10, x11, x12 hold `a`, `b`, `c` (all others 0), whose ROM repeats the word `code` and
    whose RAM repeats the word `data` at every aligned address; PC 0. -/
def witness (a b c code data : Word) : State where
  pc := 0
  regFile := fun i => if i = 10 then a else if i = 11 then b else if i = 12 then c else 0
  rom := fun x => code.extractLsb' (8 * (x.toNat % 4)) 8
  mem := fun x => data.extractLsb' (8 * (x.toNat % 4)) 8

theorem compress_word12 :
    (readWords (witness 0 0 0 0 (IV 6)).mem (0x400000#32 + 32) 16)[12] = (IV 6 ^^^ IV 4) ^^^ IV 4 := by decide

theorem compress_word14 :
    (readWords (witness 0 0 0 0 (IV 6)).mem (0x400000#32 + 32) 16)[14] =
      (if false then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6 := by decide

theorem compress_assumptions (control : Word) :
    BlakeCompressAssumptions control (witness 0x400000#32 0x400080#32 control 0 (IV 6)) 0x400000#32 0x400080#32
      (IV 6 ^^^ IV 4) false :=
  ⟨by unfold Buffer; decide, by unfold Buffer; decide, by unfold Apart; decide, rfl, rfl, rfl, compress_word12,
    compress_word14⟩

theorem hash_assumptions (control code : Word) :
    BlakeHashAssumptions control (witness 0x400000#32 0x400080#32 control code 0) 0x400000#32 0x400080#32 :=
  ⟨by unfold Buffer; decide, by unfold Buffer; decide, by unfold Apart; decide, rfl, rfl, rfl⟩

theorem g_assumptions (control : Word) :
    BlakeGAssumptions control (witness 0x400000#32 0x400040#32 control 0 0) 0x400000#32 0x400040#32 :=
  ⟨by unfold Buffer; decide, by unfold Buffer; decide, by decide, rfl, rfl, rfl⟩

theorem keccak_assumptions : KeccakAssumptions (witness 0 0x400000#32 0 0 0) 0x400000#32 :=
  ⟨by unfold Buffer; decide, rfl, rfl⟩

end RV.Deleg.NonVacuous
