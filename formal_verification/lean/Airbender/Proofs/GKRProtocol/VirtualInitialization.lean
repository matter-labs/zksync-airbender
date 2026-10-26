import Airbender.Proofs.GKRProtocol.WindowedPublic

namespace Airbender.Compiler
open Airbender
set_option warningAsError true

/-- Row values of the native four-byte initialization virtual polynomials. -/
def initializationVirtualOracle (row : Nat) (fallback : GKRAddress → Source.BaseField) :
    GKRAddress → Source.BaseField
  | .VirtualSetup .InitsAndTeardownsLow => (Initialization.addressLo row : Nat)
  | .VirtualSetup .InitsAndTeardownsHigh => (row / 16384 : Nat)
  | address => fallback address

theorem initialization_virtual_low (row : Nat) (fallback : GKRAddress → Source.BaseField) :
    initializationVirtualOracle row fallback (.VirtualSetup .InitsAndTeardownsLow) =
      (Initialization.addressLo row : Nat) := rfl

theorem initialization_virtual_high (row : Nat) (fallback : GKRAddress → Source.BaseField) :
    initializationVirtualOracle row fallback (.VirtualSetup .InitsAndTeardownsHigh) =
      (row / 16384 : Nat) := rfl

end Airbender.Compiler
