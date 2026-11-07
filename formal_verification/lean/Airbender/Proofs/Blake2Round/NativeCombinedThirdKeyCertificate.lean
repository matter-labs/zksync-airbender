import Airbender.Proofs.Blake2Round.NativeCombinedKeyData

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs NativeXorKeyHelpers
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

open CombinedKeyData

theorem combined_third_template (group : Fin 16) :
    ∀ offset : Fin 8, thirdTemplate[8 * group.val + offset.val]? = some group.val := by
  fin_cases group
  all_goals dsimp only [thirdTemplate]
  all_goals simp only [raw_get_append,  raw_literal_size,
    List.length_cons, List.length_nil, Nat.reduceAdd]
  all_goals decide +kernel


end Airbender.Blake2Round.Proofs
