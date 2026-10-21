import Airbender.Proofs.Blake2Round.NativeCombinedSecondKeyPart0
import Airbender.Proofs.Blake2Round.NativeCombinedSecondKeyPart1
import Airbender.Proofs.Blake2Round.NativeCombinedSecondKeyPart2
import Airbender.Proofs.Blake2Round.NativeCombinedSecondKeyPart3
import Airbender.Proofs.Blake2Round.NativeCombinedSecondKeyPart4
import Airbender.Proofs.Blake2Round.NativeCombinedSecondKeyPart5
import Airbender.Proofs.Blake2Round.NativeCombinedSecondKeyPart6
import Airbender.Proofs.Blake2Round.NativeCombinedSecondKeyPart7
import Airbender.Proofs.Blake2Round.NativeCombinedThirdKeyCertificate

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs NativeXorKeyHelpers
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

open CombinedKeyData

private theorem second_template (group : Fin 8) :
    ∀ offset : Fin 128, secondTemplate[128 * group.val + offset.val]? = some group.val := by
  fin_cases group
  · exact second_template_0
  · exact second_template_1
  · exact second_template_2
  · exact second_template_3
  · exact second_template_4
  · exact second_template_5
  · exact second_template_6
  · exact second_template_7

theorem combined_second_optional (n : Nat) (hn : n < 1024) :
    secondTemplate[n]? = some (n / 128) := by
  have get := second_template ⟨n / 128, by omega⟩ ⟨n % 128, by omega⟩
  have index : 128 * (n / 128) + n % 128 = n := by omega
  simpa only [index] using get

theorem combined_third_optional (n : Nat) (hn : n < 128) :
    thirdTemplate[n]? = some (n / 8) := by
  have get := combined_third_template ⟨n / 8, by omega⟩ ⟨n % 8, by omega⟩
  have index : 8 * (n / 8) + n % 8 = n := by omega
  simpa only [index] using get

end Airbender.Blake2Round.Proofs
