import Airbender.Review.Helpers.Tables.Lookups

namespace Airbender.Verification

def subwordLoadLimbs (byte : Bool) (key : Nat) : Nat × Nat :=
  let half := key % 65536
  let value := if byte then half / (if key / 131072 % 2 = 1 then 256 else 1) % 256 else half
  let negative := key / 65536 % 2 = 1 ∧ (if byte then 128 else 32768) ≤ value
  (value + (if byte && negative then 65280 else 0), if negative then 65535 else 0)

def subwordDataRow (key lo hi tag : Nat) : Vector Nat 9 :=
  #v[key, lo, hi, 0, 0, 0, 0, 0, tag]

/-- Tag 30 clears the selected old byte; tag 29 places the source's low byte. -/
def subwordStoreContribution (clear : Bool) (key : Nat) : Nat :=
  let half := key % 65536
  if clear then
    if key / 65536 % 2 = 1 then half % 256 else half - half % 256
  else (key % 256) * (if key / 65536 % 2 = 1 then 256 else 1)

/-- Original axiom-free mathematical interface. Native table contents are
    imported separately and proved to have this characterization. -/
def subwordRow (program : Nat → BitVec 32) (index : Fin 13238273) : Vector Nat 9 :=
  let n := index.val
  if n = 0 then subwordDataRow 0 0 0 0
  else if n < 131073 then
    let key := n - 1
    subwordDataRow key (subwordStoreContribution false key) 0 29
  else if n < 262145 then
    let key := n - 131073
    subwordDataRow key (subwordStoreContribution true key) 0 30
  else if n < 393217 then
    let key := n - 262145
    let data := subwordLoadLimbs false key
    subwordDataRow key data.1 data.2 42
  else if n < 655361 then
    let key := n - 393217
    let data := subwordLoadLimbs true key
    subwordDataRow key data.1 data.2 43
  else if n < 4849665 then
    let i := n - 655361
    let address := 4 * (i / 4)
    let signed := i / 2 % 2
    let half := (program (i / 4)).toNat / (if i % 2 = 1 then 65536 else 1) % 65536
    let data := subwordLoadLimbs false (half + 65536 * signed)
    subwordDataRow (address + 4194304 * signed + 8388608 * (i % 2)) data.1 data.2 44
  else
    let i := n - 4849665
    let address := 4 * (i / 8)
    let signed := i / 4 % 2
    let highHalf := i / 2 % 2
    let highByte := i % 2
    let half := (program (i / 8)).toNat / (if highHalf = 1 then 65536 else 1) % 65536
    let data := subwordLoadLimbs true (half + 65536 * signed + 131072 * highByte)
    subwordDataRow (address + 4194304 * signed + 8388608 * highHalf + 16777216 * highByte)
      data.1 data.2 45

/-- Compatibility spelling used by imported-row characterization proofs. -/
abbrev referenceSubwordRow := subwordRow

end Airbender.Verification
