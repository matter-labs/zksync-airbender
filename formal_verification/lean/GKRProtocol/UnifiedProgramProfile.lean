import GKRProtocol.Source
import Airbender.Proofs.BabyBear
import GKRProtocol.PublicProgram
import Airbender.Review.Helpers.UnifiedReduced.Registry

namespace Airbender.Compiler.UnifiedProgramProfile
open Airbender Airbender.Trace Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536

private theorem operation_guard (index : Fin 4) :
    ((unifiedEntry index).data.funct3 : Source.BaseField) ≠ 46 := by
  fin_cases index <;> decide +kernel

theorem entry_operation (entry : UnifiedReduced.ProgramEntry) (member : entry ∈ unifiedProgram) :
    (entry.data.funct3 : Source.BaseField) ≠ 46 := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact operation_guard index

/-- The native operation field is determined by the selected public decoder
entry, independently of the values returned by the non-decoder queries. -/
theorem query_operation (w : Nat → Source.BaseField)
    (member : (decoderTable unifiedProgram .machine).Contains #[]
      (nativeDecoderQuery UnifiedReduced.importedConstraintsTraceColumns
        UnifiedReduced.importedConstraintsDecoderColumns w)) : w 10 ≠ 46 := by
  obtain ⟨entry, present, _, query⟩ := Trace.Proofs.decoder_member member
  have same := congrArg (fun fields : Vector Source.BaseField 9 => fields[7]) query
  change w 10 = (entry.data.funct3 : Source.BaseField) at same
  rw [same]
  exact entry_operation entry present

end Airbender.Compiler.UnifiedProgramProfile
