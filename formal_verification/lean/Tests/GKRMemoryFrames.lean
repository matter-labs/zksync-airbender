import Airbender.Proofs.GKRProtocol.FramedWitnessNative.AddSubUncached

namespace Tests.GKRMemoryFrames
open Airbender Airbender.Compiler
set_option warningAsError true

/-- A source memory field that read the chosen lookup counter would not frame. -/
theorem rejects_memory_counter_alias :
    sourcePortFrameCheck (List.ofFn CounterFrameNative.AddSubUncached.native.slots)
      FullArithmeticNative.AddSubUncached.native.inputBank FullArithmeticNative.AddSubUncached.native.bank
      (.BaseLayerWitness (TableNative.AddSubUncached.native.multiplicityColumns.get ⟨0, by decide⟩)) = false := by
  decide +kernel

/-- A lookup setup value cannot silently become an external RAM source field. -/
theorem rejects_lookup_setup_as_memory_source :
    sourcePortFrameCheck [] FullArithmeticNative.AddSubUncached.native.inputBank
      FullArithmeticNative.AddSubUncached.native.bank (.VirtualSetup .RangeCheckTimestamp) = false := by
  decide +kernel

/-- Initialization address limbs retain the external source interface. -/
theorem accepts_external_initialization_address :
    sourcePortFrameCheck [] FullArithmeticNative.AddSubUncached.native.inputBank
      FullArithmeticNative.AddSubUncached.native.bank (.VirtualSetup .InitsAndTeardownsLow) = true := by
  decide +kernel

theorem inactive_memory_history_is_unobservable :
    maskProduct (0 : Source.BaseField) 3 = maskProduct 0 7 := by decide +kernel

theorem rejects_erasing_active_memory_effect :
    maskProduct (1 : Source.BaseField) 3 ≠ maskProduct 1 7 := by decide +kernel

end Tests.GKRMemoryFrames
