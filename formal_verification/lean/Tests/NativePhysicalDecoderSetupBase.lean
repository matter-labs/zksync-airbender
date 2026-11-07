import Airbender.Review.Circuits.ReducedMachine.PhysicalDecoderSetupTheorems
import Tests.NativeDecoderTable

namespace Airbender.Tests.NativePhysicalDecoderSetup
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.ReducedMachine.NativePhysicalDecoderSetup Airbender.ReducedMachine.NativeDecoderTableArguments
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

def emptySetup : SparseDecoderSetup UnifiedMode := ⟨[],1048576⟩

theorem public_empty_image (before : Reference.RiscV.Sail.State) :
    unifiedDecoderSetupImage before 0 20 = some emptySetup := rfl

theorem empty_ordinary (i : Nat) : ordinaryRow emptySetup i = Vector.replicate 10 (-1) := by
  by_cases inside : i < sliceSize emptySetup
  · rw [NativePhysicalDecoderSetupProofs.slice_row _ _ inside]
    simp only [SparseDecoderSetup.row,emptySetup,List.getElem?_nil,Option.bind_none]
  · exact NativePhysicalDecoderSetupProofs.tail_row _ _ (Nat.le_of_not_gt inside)

theorem entire_physical_tail : ordinaryRow emptySetup 1048576 = Vector.replicate 10 (-1) ∧
    ordinaryRow emptySetup 8388606 = Vector.replicate 10 (-1) := ⟨empty_ordinary 1048576,empty_ordinary 8388606⟩




end Airbender.Tests.NativePhysicalDecoderSetup
