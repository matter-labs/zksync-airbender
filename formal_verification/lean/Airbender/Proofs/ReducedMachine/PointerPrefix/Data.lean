import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness
import Airbender.Review.Circuits.ReducedMachine.InitializationBoundary

namespace Airbender.NativePointerPrefixProofs
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Verification
abbrev F := ZMod mersenne31Modulus

/-- Independent deterministic pointer - setup row, checked against native BODY. -/
def baseValues : Array Nat := #[
  0,0,4,0,1,0,0,11,0,128,0,0,9,4,0,8,
  0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,128,0,11,0,128,
  0,4,0,1227138194,0,2147450879,0,0,0,0,0,0,0,128,0,0,
  0,0,0,0,1,0,0,0,0,4,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,128,0,128,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,1,4,0,1,0,0,1,0
]
def pcInverses : Array Nat := #[1227138194,1801116374,241970450,896194221,906475674,1893078033,346014073,693414549,491232786,292960889,723970736,1046688409,1603857167,1459521453,1299949819,67141664,2009026256,963093798,1241479127,1791024196,800663745,2009902683,31468688,1146691948,1109611981,58780768,1304842153,1125964960,1435912216,1027355704,14806383,1592719227,1787063367,905719288,1868720593,1072395377,1127767189,619276951,258926485,1735403031,745798220]

/-- Actual state/message RAM addresses; all40 positions remain distinct. -/
def ramAddress (index : Nat) : Nat := if index < 24 then 4 * index else 128 + 4*(index - 24)

/-- Forty ADDI x11,x0,128 rows, then CSRRW x0,1991,x0. Actual raw times,
    previous reads, PC carry auxiliaries and initialization records are retained.
    First row has padding init; the remaining40 carry the full RAM records. -/
def assignment (row : Fin 41) (column : Nat) : F :=
  let i := row.val
  let base := if i = 40 then NativeCSRPositiveWitness.values else baseValues
  let clock := 4 + 4 * i
  let value :=
    if column = 0 then 4 * i else
    if column = 2 then clock else
    if column = 13 ∨ column = 49 ∨ column = 73 then 4 * i + 4 else
    if column = 15 then clock + 4 else
    if 0 < i ∧ i < 40 ∧ column = 41 then 128 else
    if column = 51 then (pcInverses[i]?).getD 0 else
    if column = 132 then (if i = 0 then 0 else 4 * i + 1) else
    if column = 135 then clock else
    if column = 138 then (if i = 0 then 0 else if i = 40 then clock + 1 else 4 * i + 2) else
    if 0 < i ∧ i < 40 ∧ column = 122 then 65536 + ramAddress (i - 1)-ramAddress i else
    if 0 < i ∧ i < 40 ∧ column = 123 then 65535 else
    if 0 < i ∧ i < 40 ∧ (column = 124 ∨ column = 125) then 1 else
    if 0 < i ∧ column = 126 then ramAddress (i - 1) else
    if 0 < i ∧ column = 130 then 167 else
    (base[column]?).getD 0
  (value : Nat)
end Airbender.NativePointerPrefixProofs
