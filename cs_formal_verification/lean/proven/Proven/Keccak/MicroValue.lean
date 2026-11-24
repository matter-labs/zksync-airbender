module
public import Proven.Keccak.MicroOperations

@[expose] public section

namespace Airbender.Keccak.Proofs
set_option warningAsError true

def iotaValue (control : ControlState) (read : Fin 6 → Nat) (lane : Fin 6) : Nat :=
  if h : control.iteration.val = 0 ∧ lane.val = 0 ∧ 0 < control.round.val then
    read lane ^^^ Specs.Keccak256.roundConstants[Fin.ofNat 24 (control.round.val - 1)].toFin
  else read lane

def microValue (control : ControlState) (read : Fin 6 → Nat) (lane : Fin 6) : Nat :=
  if control.mode = 0 then
    if lane.val < 5 then iotaValue control read lane else
      iotaValue control read 0 ^^^ read 1 ^^^ read 2 ^^^ read 3 ^^^ read 4
  else if control.mode = 1 then
    if lane = 0 then read 0 ^^^ rotLeft64 (read 2) 1
    else if lane = 2 then read 2 ^^^ rotLeft64 (read 4) 1
    else if lane = 5 then rotLeft64 (read 0) 1 else read lane
  else if control.mode = 2 then
    if lane = 1 then read 1 ^^^ rotLeft64 (read 3) 1
    else if lane = 3 then read 3 ^^^ read 5
    else if lane = 4 then read 4 ^^^ rotLeft64 (read 1) 1 else read lane
  else if control.mode = 3 then
    if lane.val < 5 then read lane ^^^ read 5 else read 5
  else if control.mode = 4 then
    if h : lane.val < 5 then rotLeft64 (read lane) rhoRotations[control.iteration][lane.val] else read 5
  else if control.mode = 5 then
    if lane = 0 then read 0 ^^^ ((not64 (read 1)) &&& read 2)
    else if lane = 1 then read 1 ^^^ ((not64 (read 2)) &&& read 3)
    else if lane = 4 then (not64 (read 0)) &&& read 1
    else if lane = 5 then read 0 else read lane
  else
    if lane = 0 then read 0 ^^^ read 3
    else if lane = 1 then read 1 ^^^ ((not64 (read 2)) &&& read 0)
    else if lane = 2 then read 2 ^^^ ((not64 (read 0)) &&& read 4) else read lane

/-- Entry `i` of the selected column after Iota: the read lane, with the round constant on lane 0 of
    column 0. -/
private theorem iota_entry (control : ControlState) (bound : control.round.val < 25)
    (read : Fin 6 → Nat) (i : Fin 5) :
    (iotaState (columnState (Vector.ofFn read) control.iteration) (Fin.ofNat 25 control.round.val))[
      5 * control.iteration.val + i.val]'(by omega) = iotaValue control read ⟨i.val, by omega⟩ := by
  have column : (columnState (Vector.ofFn read) control.iteration)[5 * control.iteration.val + i.val]'
      (by omega) = read ⟨i.val, by omega⟩ := by
    have index : Fin.ofNat 6 ((5 * control.iteration.val + i.val) % 5) = ⟨i.val, by omega⟩ :=
      Fin.ext (by simp only [Fin.val_ofNat]; omega)
    simp only [columnState, Vector.getElem_ofFn,
      show (5 * control.iteration.val + i.val) / 5 = control.iteration.val by omega, ↓reduceIte, index,
      Fin.getElem_fin]
  have round : Fin.ofNat 25 control.round.val = ⟨control.round.val, bound⟩ :=
    Fin.ext (by simp only [Fin.val_ofNat]; omega)
  have constant : Fin.ofNat 24 (control.round.val - 1) = ⟨control.round.val - 1, by omega⟩ :=
    Fin.ext (by simp only [Fin.val_ofNat]; omega)
  rw [round]
  unfold iotaState iotaValue
  by_cases positive : 0 < control.round.val
  · by_cases first : control.iteration.val = 0 ∧ i.val = 0
    · have zero : 5 * control.iteration.val + i.val = 0 := by omega
      simp only [zero] at column
      simp only [positive, ↓reduceDIte, Specs.Keccak256.iota, Vector.getElem_set, ↓reduceIte, column,
        first, and_self, constant, Fin.getElem_fin]
    · have nonzero : ¬0 = 5 * control.iteration.val + i.val := by omega
      simp only [positive, ↓reduceDIte, Specs.Keccak256.iota, Vector.getElem_set, nonzero, ↓reduceIte, column,
        and_true, first]
  · simp only [positive, ↓reduceDIte, column, and_false]

private theorem parity_entries (state : Vector Nat 25) (column : Fin 5) :
    (Specs.Keccak256.thetaC state)[column.val] =
      state[5 * column.val] ^^^ state[5 * column.val + 1] ^^^
      state[5 * column.val + 2] ^^^ state[5 * column.val + 3] ^^^ state[5 * column.val + 4] := by
  fin_cases column <;> rfl

private theorem mode_zero_value (control : ControlState) (bound : control.round.val < 25)
    (read : Fin 6 → Nat) (lane : Fin 6) (mode : control.mode = 0) :
    (microWrites control (Vector.ofFn read))[lane] = microValue control read lane := by
  simp only [microWrites, microValue, mode, ↓reduceIte, Fin.getElem_fin, Vector.getElem_ofFn]
  by_cases small : lane.val < 5
  · simp only [small, ↓reduceDIte, ↓reduceIte]
    exact iota_entry control bound read ⟨lane.val, small⟩
  · simp only [small, ↓reduceDIte, ↓reduceIte]
    rw [parity_entries]
    have e0 := iota_entry control bound read 0
    have e1 := iota_entry control bound read 1
    have e2 := iota_entry control bound read 2
    have e3 := iota_entry control bound read 3
    have e4 := iota_entry control bound read 4
    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
      Nat.add_zero] at e0 e1 e2 e3 e4
    rw [e0, e1, e2, e3, e4]
    simp [iotaValue]

theorem micro_value_eq (control : ControlState) (bound : control.round.val < 25)
    (read : Fin 6 → Nat) (lane : Fin 6) :
    (microWrites control (Vector.ofFn read))[lane] = microValue control read lane := by
  generalize mode : control.mode = selected
  fin_cases selected
  · exact mode_zero_value control bound read lane mode
  all_goals fin_cases lane
  all_goals simp [microWrites, microValue, mode]

end Airbender.Keccak.Proofs
