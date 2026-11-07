import Tests.NativePhysicalDecoderSetupBase

namespace Airbender.Tests.NativePhysicalDecoderSetup
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.ReducedMachine.NativePhysicalDecoderSetup Airbender.ReducedMachine.NativeDecoderTableArguments
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem empty_normalized_last (column : Fin 10) :
    (normalizedRow emptySetup (decoderTableLayout.traceLength-1))[column.val] =
      ((decoderTableLayout.traceLength-1 : Nat) : F) := by
  have generic := Airbender.Verification.NormalizeLastProofs.vector_constant_terminal
    decoderTableLayout.traceLength (ordinaryRow emptySetup) column (-1 : F)
    (fun i => by rw [empty_ordinary,Vector.getElem_replicate])
  change (normalizedRow emptySetup (decoderTableLayout.traceLength-1))[column.val] = _ at generic
  simpa only [nsmul_eq_mul,mul_neg,mul_one,neg_neg] using generic

theorem normalized_last_is_not_padding :
    normalizedRow emptySetup (decoderTableLayout.traceLength-1) ≠ Vector.replicate 10 (-1) := by
  have zeroColumn := empty_normalized_last (⟨0,by decide⟩ : Fin 10)
  change (normalizedRow emptySetup (decoderTableLayout.traceLength-1))[0] =
    ((decoderTableLayout.traceLength-1 : Nat) : F) at zeroColumn
  intro same
  have equality := congrArg (fun row : Vector F 10 => row[0]) same
  rw [zeroColumn] at equality
  have distinct : ((decoderTableLayout.traceLength-1 : Nat) : F) ≠ -1 := by decide +kernel
  exact distinct equality

theorem every_column_sum_zero (column : Fin 10) :
    (∑ i ∈ Finset.range decoderTableLayout.traceLength, (normalizedRow emptySetup i)[column.val]) = 0 :=
  NativePhysicalDecoderSetupProofs.normalized_sum emptySetup column

theorem small_normalizer_control :
    Airbender.Verification.normalizeLast 5 (fun i => ((i+1 : Nat) : F)) 4 = -10 := by decide +kernel
end Airbender.Tests.NativePhysicalDecoderSetup
