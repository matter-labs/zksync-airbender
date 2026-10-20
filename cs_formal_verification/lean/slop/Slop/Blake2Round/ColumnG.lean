import Slop.Blake2G.Assembly

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- Rename each column invocation's actual input and temporary columns. Its output
-- words are expressions in this artifact, not separate allocated variables.
def columnGBase {p : Nat} (call : Fin 4) (w : Nat → ZMod p) (column : Nat) : ZMod p :=
  match column with
  | 15 => w (155 + 4 * call.val) | 16 => w (157 + 4 * call.val)
  | 19 => w (171 + 4 * call.val) | 20 => w (173 + 4 * call.val)
  | 23 => w (186 + 2 * call.val) | 24 => w (187 + 2 * call.val)
  | 27 => w (#v[198, 194, 200, 196][call]) | 28 => w (#v[199, 195, 201, 197][call])
  | 33 => w (236 + 4 * call.val) | 34 => w (237 + 4 * call.val)
  | 35 => w (238 + 4 * call.val) | 36 => w (239 + 4 * call.val)
  | n => w (n + 231 + 46 * call.val)

def columnGAssignment {p : Nat} (call : Fin 4) (w : Nat → ZMod p) (column : Nat) : ZMod p :=
  Blake2G.Proofs.assemble (columnGBase call w) column

end Airbender.Blake2Round.Proofs
