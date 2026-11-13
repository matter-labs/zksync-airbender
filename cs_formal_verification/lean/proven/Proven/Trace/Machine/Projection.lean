module
public import Proven.Trace.Machine.Program
public import Mathlib.Data.Option.Basic

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Extra native instructions use only the configured arithmetic circuit. -/
theorem extra_family {config : RVMachineConfig} {instruction : RV.Instr} {data : RVMachineDecoderData}
    (fields : rvMachineExtraFields config instruction = some data) : data.family = config.arithmeticFamily := by
  cases instruction <;> simp only [rvMachineExtraFields] at fields
  all_goals try contradiction
  case delegate kind =>
    split at fields
    · cases fields
      rfl
    · cases fields
  case inputRead rd =>
    split at fields
    · cases fields
    · cases fields
      rfl
  case inputWrite source =>
    cases fields
    rfl
  case mop op rd rs1 rs2 =>
    split at fields
    · cases fields
      rfl
    · cases mask : rvModularMask op with
      | none => simp [mask] at fields
      | some value =>
        simp only [mask, Option.map_some, Option.some.injEq] at fields
        subst fields
        rfl

/-- A non-arithmetic unrolled entry comes from the existing ordinary program projection. -/
theorem unrolled_ordinary_fields {config : RVMachineConfig} {instruction : RV.Instr} {data : RVMachineDecoderData}
    (unrolled : config ≠ .unified) (family : data.family ≠ config.arithmeticFamily)
    (fields : rvMachineDecoderFields config instruction = some data) :
    ∃ ordinary, rvPooledDecoderFields instruction = some ordinary ∧
      data = RVMachineDecoderData.ofOrdinary (family := RVMachineDecoderFamily.pooled) ordinary := by
  have noExtra : rvMachineExtraFields config instruction = none := by
    cases extra : rvMachineExtraFields config instruction with
    | none => rfl
    | some native =>
      have same : native = data := by
        have selected := Option.orElse_eq_some _ _ data |>.mp (show
          (some native <|> _) = some data by simpa only [rvMachineDecoderFields, extra] using fields)
        rcases selected with equal | ⟨impossible, _⟩
        · exact Option.some.inj equal
        · cases impossible
      have arithmetic := extra_family extra
      exact False.elim (family (same ▸ arithmetic))
  have mode : (config == .unified) = false := by cases config <;> simp_all
  have fallback := Option.orElse_eq_some _ _ data |>.mp (show (none <|> _) = some data by
    simpa only [rvMachineDecoderFields, noExtra] using fields)
  rcases fallback with impossible | ⟨_, fields⟩
  · cases impossible
  simp only [mode, Bool.false_eq_true, ↓reduceIte] at fields
  change ((rvPooledDecoderFields instruction).filter fun ordinary =>
      config == .unrolledFullUnsigned ||
        (ordinary.family != .mulDiv && ordinary.family != .subwordMemory)).map
      (RVMachineDecoderData.ofOrdinary (family := RVMachineDecoderFamily.pooled)) = some data at fields
  obtain ⟨ordinary, admitted, same⟩ := Option.map_eq_some_iff.mp fields
  exact ⟨ordinary, (Option.filter_eq_some_iff.mp admitted).1, same.symm⟩

end Airbender.Trace.Machine.Proofs
