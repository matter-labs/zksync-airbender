import Airbender.Proofs.Blake2Round.NativeXorKeyHelpers
import Airbender.Proofs.Tables.LiteralPeriodicTemplate
import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs NativeXorKeyHelpers
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

namespace CombinedKeyData

literal_periodic_template secondTemplate from (xor4x3Data.columns[1]) block 0
literal_periodic_template thirdTemplate from (xor4x3Data.columns[2]) block 0

theorem second_size : secondTemplate.size = 1024 := by
  dsimp only [secondTemplate]
  simp only [  raw_size_append,
    raw_literal_size, List.length_cons, List.length_nil, Nat.reduceAdd]

theorem third_size : thirdTemplate.size = 128 := by
  dsimp only [thirdTemplate]
  simp only [  raw_size_append,
    raw_literal_size, List.length_cons, List.length_nil, Nat.reduceAdd]

end CombinedKeyData

end Airbender.Blake2Round.Proofs
