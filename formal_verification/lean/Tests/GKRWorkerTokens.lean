import GKRProtocol.MemoryTokens
import Airbender.Review.Helpers.Delegation.Requests

namespace Tests.GKRWorkerTokens
open Airbender Airbender.Compiler
set_option warningAsError true

def request : Delegation.Requests.Request babyBearModulus := ⟨1994, (5, 7)⟩

theorem marker_keeps_full_csr :
    request.issued.address = Nat.pair 0 (Nat.pair 1994 0) := by rfl

theorem marker_clock_is_not_erased : request.issued ≠ request.empty := by decide +kernel

theorem different_csr_is_a_different_token :
    request.issued ≠ (⟨1995, (5, 7)⟩ : Delegation.Requests.Request babyBearModulus).issued := by decide +kernel

theorem empty_marker_retains_virtual_address :
    request.empty.address = request.issued.address := by rfl

end Tests.GKRWorkerTokens
