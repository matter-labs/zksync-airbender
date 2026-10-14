import Airbender.Review.Trace.UnifiedReduced.PreparedHashWindows
import Airbender.Proofs.UnifiedReduced.ControlPreparation

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem hash_preparation_value (span : Delegation.Caller.HashSpan) :
    (hashPreparation span).value = span.controlStart := by
  cases span with
  | blakeG reduced => cases reduced <;> decide +kernel
  | blakeRound flags => fin_cases flags <;> decide +kernel
  | keccak => decide +kernel

theorem hash_control_register_nonzero (span : Delegation.Caller.HashSpan) :
    span.controlRegister ≠ 0 := by
  cases span with
  | blakeG _ => change (12 : BitVec 5) ≠ 0; decide
  | blakeRound _ => change (12 : BitVec 5) ≠ 0; decide
  | keccak => change (10 : BitVec 5) ≠ 0; decide

end Airbender.UnifiedReduced.Caller.Proofs
