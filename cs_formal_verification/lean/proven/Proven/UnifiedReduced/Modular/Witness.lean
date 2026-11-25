module
public import Human.Circuits.UnifiedReduced.Modular
public import Human.Circuits.UnifiedReduced.Tables.SetupRV
public import Proven.WitnessCheck
public import Proven.KernelRfl
public import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace Airbender.UnifiedReduced.Modular.Witness

/-- A modular instruction on zeroed registers at clock four, with the actual comparison and
    quotient limbs. The four branches share their PC, memory addresses and predecessor clocks. -/
def assignment {p : Nat} (op : AddSub.Modular.Opcode) (v : Nat) : ZMod p :=
  if v = op.selector + 1 then 1 else
  match v with
  | 2 | 30 => 4
  | 4 | 5 | 52 | 53 | 123 | 124 | 125 => 1
  | 6 | 38 => 2
  | 7 | 44 => 3
  | 32 => 8
  | 54 => if op = .add then 0 else 1
  | 55 => if op = .sub then 1 else 0
  | 74 => 65535
  | 75 => 34815
  | 78 => if op = .add ∨ op = .sub then 2013265921 else 0
  | _ => 0

/-- The active zero-operand FMA row witnesses the BabyBear layout independently of its soundness proof. -/
theorem babyBear_satisfiable : BabyBearResultSatisfiableClaim := by
  let w := assignment (p := babyBearModulus) .fma
  let setup := Setup.tableWith (p := babyBearModulus) (fun _ => 0)
  refine ⟨setup, w, .fma, ?_, ?_, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, rfl⟩
  · apply Verification.holds_of_checkOps (tables := List.replicate 13 Verification.range16Checked ++
      List.replicate 5 (Verification.staticChecked setup rfl))
    · rfl
    · kernel_rfl
  · intro k lo hi
    interval_cases k <;> rfl

end Airbender.UnifiedReduced.Modular.Witness
