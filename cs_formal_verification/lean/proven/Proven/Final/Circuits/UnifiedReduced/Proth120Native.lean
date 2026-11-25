module
public import Proven.Compiler.Proth120Decoder
public import Proven.Compiler.Proth120Lookups
public import Proven.Compiler.Proth120NativeWitness

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120

theorem native_arithmetic : NativeArithmeticClaim := fun _ _ => equations_of_native

theorem native_arithmetic_satisfiable : NativeArithmeticSatisfiableClaim :=
  ⟨Witness.nativePhysical, Witness.assignment .fma, Witness.nativeArithmetic⟩

private theorem assert_member {α : Type} {e : Expression α} {ops : List (FlatOperation α)}
    (h : e ∈ FlatOperation.constraints ops) : FlatOperation.assert e ∈ ops := by
  induction ops using FlatOperation.induct with
  | empty => cases h
  | assert x rest ih =>
    rcases List.mem_cons.mp h with rfl | mem
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih mem)
  | lookup x rest ih => exact List.mem_cons_of_mem _ (ih h)

theorem native_row : NativeRowClaim := by
  intro setup decode rows physical logical arithmetic matched
  refine ⟨FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr ⟨?_, native_lookup_holds arithmetic matched⟩,
    native_decoder_holds arithmetic matched⟩
  intro e mem
  have same : FlatOperation.constraints (clockConstraints setup) = FlatOperation.constraints (importedConstraints setup) := rfl
  rw [same] at mem
  exact equations_of_native arithmetic setup e (assert_member mem)

theorem native_row_satisfiable : NativeRowSatisfiableClaim :=
  ⟨_, _, Witness.nativeRows, Witness.nativePhysical, Witness.assignment .fma,
    Witness.nativeArithmetic, Witness.nativeMatched, rfl⟩

end Airbender.UnifiedReduced.Proth120
