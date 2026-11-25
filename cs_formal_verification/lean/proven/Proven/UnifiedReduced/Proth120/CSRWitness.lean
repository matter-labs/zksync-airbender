module
public import Human.Circuits.UnifiedReduced.Proth120Input
public import Proven.UnifiedReduced.Proth120.Witness

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120.CSRWitness
open Trace Verification

/-- For reads the native destination is x3 and its response is seven. Writes have the NOP row. -/
def assignment (read : Bool) (v : Nat) : ZMod proth120Modulus := match v with
  | 2 | 30 | 40 => 4
  | 4 | 123 | 124 | 125 => 1
  | 7 | 44 => if read then 3 else 0
  | 11 => if read then 0 else 1
  | 19 => if read then 1 else 0
  | 32 => 8
  | 46 => if read then 0 else 5
  | 50 => if read then 7 else 0
  | 78 => 2013265921
  | _ => 0

def initial (read : Bool) : _root_.RV.State where
  pc := 0
  regFile _ := 0
  mem _ := 0
  rom a := match a.toNat with
    | 0 => if read then 0xf3 else 0x73
    | 1 => if read then 0x11 else 0x90
    | 3 => 0x7c
    | _ => 0
  input := [7, 11]

def result (read : Bool) := if read then (initial read).setReg 3 7 else initial read
def cells : List Cell := [.register 0, .register 3]

theorem inputs (read : Bool) : CSRInputs cells 0 (assignment read) (initial read) (result read) read where
  constraints := by
    apply holds_of_checkOps (tables := List.replicate 15 range16Checked ++
      List.replicate 5 (Witness.checked (ROM.wordsRV (initial read))))
    · rfl
    · cases read <;> kernel_rfl
  active := rfl
  fetch := ⟨rfl, by change 0 + 4 ≤ romEnd; decide⟩
  decoded := by
    cases read
    · exact ⟨1, by decide, by kernel_rfl, by kernel_rfl⟩
    · exact ⟨3, by decide, by kernel_rfl, by kernel_rfl⟩
  response := by intro isRead; subst read; kernel_rfl
  bounded := by cases read <;> exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide⟩
  aligned := by
    intro c h
    rcases List.mem_cons.mp h with rfl | h
    · trivial
    · obtain rfl := List.mem_singleton.mp h
      trivial
  history := by
    apply RVHistory.cons (cell := .register (if read then 3 else 0)) (middle := initial read)
    · apply RVHistory.cons (cell := .register 0) (middle := initial read)
      · exact RVHistory.cons (RVHistory.nil _) (.register 0) (by simp [cells]) rfl rfl rfl
      · simp [cells]
      all_goals rfl
    · cases read <;> simp [cells]
    all_goals cases read <;> kernel_rfl

theorem clocks (read : Bool) : FlatOperation.ConstraintsHoldFlat (environment (assignment read))
    (importedConstraintsTimestampLookups (p := proth120Modulus)) := by
  apply holds_of_checkOps (tables := List.replicate 8 timestampChecked)
  · rfl
  · cases read <;> kernel_rfl

end Airbender.UnifiedReduced.Proth120.CSRWitness
