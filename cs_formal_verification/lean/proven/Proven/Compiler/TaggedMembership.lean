module
public import Proven.Compiler.FixedMembership

@[expose] public section
namespace Airbender.Compiler.NativePublicSetup.Proofs
open Airbender Trace NativeArithmetic Metadata
set_option warningAsError true

/-- Read one field of an independently interpreted native generic row. -/
noncomputable def genericCell (initial : RV.State) (program : List RVMachineProgramEntry)
    (family : RVMachineDecoderFamily) (index : NativeSetupIndex family) (column : Nat) : F :=
  (rows initial program family 0 index).getD column 0

/-- A fixed discriminator excludes public decoder slots and zero commitment padding. -/
theorem fixed_of_tag (initial : RV.State) (program : List RVMachineProgramEntry)
    (family : RVMachineDecoderFamily) (isTagged : tagged family = true)
    (index : NativeSetupIndex family) (tag : F) (notDecoder : tag ≠ 46) (notZero : tag ≠ 0)
    (selected : genericCell initial program family index (width family - 1) = tag) :
    ∃ position < offset family, rows initial program family 0 index =
      fixedRow family (ROM.wordsRV initial) position := by
  change ((genericRow family initial program index.val)[width family - 1]?).getD 0 = tag at selected
  unfold genericRow at selected
  dsimp only at selected
  rw [offset_binding, width_binding] at selected
  by_cases isFixed : index.val < offset family
  · refine ⟨index.val, isFixed, ?_⟩
    change genericRow family initial program index.val = _
    unfold genericRow
    dsimp only
    rw [offset_binding, ite_eq_left isFixed]
  · rw [ite_eq_right isFixed] at selected
    by_cases decoder : index.val - offset family < decoderCapacity
    · rw [ite_eq_left decoder, decoder_tag family isTagged] at selected
      exact False.elim (notDecoder selected.symm)
    · rw [ite_eq_right decoder, isTagged] at selected
      have zero : (0 : F) = tag := by
        by_cases positive : 0 < width family <;>
          simpa [List.getElem?_replicate, positive] using selected
      exact False.elim (notZero zero.symm)

end Airbender.Compiler.NativePublicSetup.Proofs
