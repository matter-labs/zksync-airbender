import Human.SpecBlake

/-! # The Merkle path the program checks

From the transcript seed (the Blake2s digest of the five input words) to a root: per level the sibling and on which
side the node is, the parent being the verifier's two-to-one hash. Root, depth and path are input words. -/

namespace Spec
open RV (Word)

/-- The verifier's two-to-one hash: Blake2s (7 rounds) of the 64-byte block `l ‖ r`, the last and only block. (What
Airbender's round-function delegation computes in compression mode.) -/
def hash2 (l r : Vector Word 8) : Vector Word 8 :=
  compress (Vector.ofFn configuredIV) (l ++ r) 64#32 true

/-- One level of a path: a side word (nonzero: the node is the right child) and the sibling. -/
abbrev MerkleStep := Word × Vector Word 8

/-- The root a path leads to from `leaf`. -/
def merkleRoot (leaf : Vector Word 8) (path : List MerkleStep) : Vector Word 8 :=
  path.foldl (fun n (side, sib) => if side ≠ 0 then hash2 sib n else hash2 n sib) leaf

/-- How the program reads a path to `root`: the root (8 words), the depth, then per level the side word and the
sibling (8 words). -/
def pathInput (root : Vector Word 8) (path : List MerkleStep) : List Word :=
  root.toList ++ BitVec.ofNat 32 path.length :: path.flatMap fun (side, sib) => side :: sib.toList

/-- The path from the transcript seed of the input `w` (the Blake2s digest of its five words) leads to `root`. -/
def pathOK (w : Vector Word 5) (root : Vector Word 8) (path : List MerkleStep) : Prop :=
  merkleRoot (blake5 w) path = root

end Spec
