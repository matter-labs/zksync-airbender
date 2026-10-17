import Airbender.Review.Circuits.Initialization.Theorems
import Airbender.Proofs.Initialization.Boundary
import Airbender.Proofs.BabyBear

namespace Tests.Initialization
open Airbender Airbender.Initialization
set_option warningAsError true
set_option Elab.async false

private def unitParameters : Parameters babyBearModulus (ZMod babyBearModulus) :=
  ⟨RingHom.id _, 0, fun _ => 0, fun set => set⟩

/-- Non-vacuity on every native row, without allocating either native domain. -/
theorem unit_accepted (artifact : Artifact) :
    Accepted artifact unitParameters (fun _ _ => 0) (fun _ _ => 1) := by
  intro row gate _
  cases gate <;> simp [Gate.Sat, Leaf.factor, unitParameters]

example : Accepted standalone unitParameters (fun _ _ => 0) (fun _ _ => 1) :=
  unit_accepted standalone

example : Accepted unified unitParameters (fun _ _ => 0) (fun _ _ => 1) :=
  unit_accepted unified

private def badStandalone : Wires (ZMod babyBearModulus) :=
  fun port _ => if port = standalone.terminal.output then 2 else 1

example : ¬ Accepted standalone unitParameters (fun _ _ => 0) badStandalone := by
  intro accepted
  have wrong := accepted ⟨0, by decide⟩ (.product ⟨3, 0⟩ ⟨2, 0⟩ ⟨2, 1⟩) (by decide +kernel)
  norm_num [Gate.Sat, badStandalone, standalone, Tree.output] at wrong
  exact (by decide : (2 : ZMod babyBearModulus) ≠ 1) wrong

private def valueParameters : Parameters babyBearModulus (ZMod babyBearModulus) :=
  ⟨RingHom.id _, 0, fun i => if i = 4 then 1 else 0, fun set => set⟩

private def noncanonical (column : Nat) : Raw babyBearModulus :=
  fun row index => if row = 0 ∧ index = column then 65537 else 0

private def standaloneWires : Wires (ZMod babyBearModulus) := fun port row =>
  if row = 0 ∧ port ∈ [⟨1, 1⟩, ⟨2, 0⟩, ⟨3, 0⟩] then 65538 else 1

/-- A raw value above 16 bits is accepted by the actual 14-gate graph. -/
theorem standalone_noncanonical_accepted :
    Accepted standalone valueParameters (noncanonical 0) standaloneWires := by
  intro row gate member
  have cases := member
  simp only [standalone, List.mem_cons, List.not_mem_nil, or_false] at cases
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    (by_cases zero : row.val = 0 <;> norm_num [Gate.Sat, Leaf.factor, Leaf.time, Leaf.value, valueParameters,
      noncanonical, standaloneWires, Port.mk.injEq, Fin.ext_iff, zero])

example : standaloneWires standalone.terminal.output 0 = 65538 ∧
    standaloneWires standalone.initial.output 0 = 1 := by decide +kernel

example : ((Leaf.mk .terminal 0 ⟨2, 3, 0, 1⟩).value (noncanonical 0) 0).1.val = 65537 := by
  norm_num [Leaf.value, noncanonical, ZMod.val_ofNat, babyBearModulus]

private def unifiedWires : Wires (ZMod babyBearModulus) := fun port row =>
  if row = 0 ∧ port ∈ [⟨1, 6⟩, ⟨2, 23⟩, ⟨3, 14⟩, ⟨4, 8⟩] then 65538 else 1

theorem unified_noncanonical_accepted :
    Accepted unified valueParameters (noncanonical 30) unifiedWires := by
  intro row gate member
  have cases := member
  simp only [unified, List.mem_cons, List.not_mem_nil, or_false] at cases
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (by_cases zero : row.val = 0 <;> norm_num [Gate.Sat, Leaf.factor, Leaf.time, Leaf.value, valueParameters,
      noncanonical, unifiedWires, Port.mk.injEq, Fin.ext_iff, zero])

example : unifiedWires unified.terminal.output 0 = 65538 ∧
    unifiedWires unified.initial.output 0 = 1 := by decide +kernel

/-- Swapping the two phases changes the actual boundary product. -/
example : unifiedWires unified.terminal.output 0 ≠ unifiedWires unified.initial.output 0 := by
  change (65538 : ZMod babyBearModulus) ≠ 1
  decide +kernel

/-- The inline RAM roots are not the ordinary RAM permutation roots 6/7. -/
example : unified.terminal.output = ⟨4, 8⟩ ∧ unified.initial.output = ⟨4, 9⟩ := by decide +kernel

example : addressLo (standalone.layout.rows - 1) = 65532 ∧
    addressHi standalone.layout unitParameters 7 (standalone.layout.rows - 1) = 8191 := by
  decide +kernel

example : addressLo (unified.layout.rows - 1) = 65532 ∧
    addressHi unified.layout unitParameters 1 (unified.layout.rows - 1) = 1023 := by
  decide +kernel

/-- The actual teardown mapping cannot be replaced by a zero initial token. -/
example : ((Leaf.mk .terminal 0 ⟨2, 3, 0, 1⟩).token standalone.layout
    valueParameters (noncanonical 0) 0).value ≠
    ((Leaf.mk .initial 0 ⟨2, 3, 0, 1⟩).token standalone.layout
      valueParameters (noncanonical 0) 0).value := by decide +kernel

end Tests.Initialization
