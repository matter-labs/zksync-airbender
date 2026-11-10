import Airbender.Proofs.Blake2Round.NativeCombinedKeyData

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs NativeXorKeyHelpers CombinedKeyData
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

theorem second_template_5 :
    ∀ offset : Fin 128, secondTemplate[128 * 5 + offset.val]? = some 5 := by
  dsimp only [secondTemplate]
  simp only [raw_get_append, raw_size_append, raw_literal_size,
    List.length_cons, List.length_nil, Nat.reduceAdd]
  decide +kernel

end Airbender.Blake2Round.Proofs
