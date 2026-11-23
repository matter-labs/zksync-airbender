module
public import Proven.Trace.Machine.ExtraShapes

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Machine metadata is extra metadata or the unchanged ordinary projection for the configured CPU. -/
theorem machine_fields_cases {config : RVMachineConfig} {instruction : RV.Instr} {data : RVMachineDecoderData}
    (fields : rvMachineDecoderFields config instruction = some data) :
    rvMachineExtraFields config instruction = some data ∨
    (config = .unified ∧ ∃ ordinary : DecoderData UnifiedFamily, UnifiedReduced.rvDecoderFields instruction = some ordinary ∧
      data = RVMachineDecoderData.ofOrdinary (family := fun _ => .unified) ordinary) ∨
    (config ≠ .unified ∧ ∃ ordinary : DecoderData PooledFamily, rvPooledDecoderFields instruction = some ordinary ∧
      data = RVMachineDecoderData.ofOrdinary (family := RVMachineDecoderFamily.pooled) ordinary) := by
  have choice := Option.orElse_eq_some _ _ data |>.mp (show (_ <|> _) = some data by
    exact fields)
  rcases choice with extra | ⟨_, ordinary⟩
  · exact Or.inl extra
  · by_cases unified : config = .unified
    · subst config
      simp only [beq_self_eq_true, ↓reduceIte] at ordinary
      obtain ⟨native, projected, same⟩ := Option.map_eq_some_iff.mp ordinary
      exact Or.inr (Or.inl ⟨rfl, native, projected, same.symm⟩)
    · have mode : (config == .unified) = false := by cases config <;> simp_all
      simp only [mode, Bool.false_eq_true, ↓reduceIte] at ordinary
      obtain ⟨native, admitted, same⟩ := Option.map_eq_some_iff.mp ordinary
      exact Or.inr (Or.inr ⟨unified, native, (Option.filter_eq_some_iff.mp admitted).1, same.symm⟩)

end Airbender.Trace.Machine.Proofs
