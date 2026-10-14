import Human.RV32
import Human.Spec
import Image
open RV

/-! Sanity check of human/RV32 (compiled, not a proof): run the image concretely from address 0 for a few inputs
and compare a0, a1 with a direct computation. Prints one line per input and exits 1 on a mismatch. -/

def mem0 (input : Word) : Word → BitVec 8 := fun a =>
  if h : a.toNat < Image.bytes.size then Image.bytes[a.toNat]
  else if a.toNat / 4 = Image.INPUT / 4 then (input >>> (8 * (a.toNat % 4))).setWidth 8 else 0

def s0 (input : Word) : State := { pc := 0, regFile := fun _ => 0, mem := mem0 input }

def P : Nat := 2 ^ 31 - 1

/-- Reference: (3x + 1 mod 2^32, ∑ cᵢ xⁱ mod P). -/
def expected (x : Nat) : Nat × Nat :=
  ((3 * x + 1) % 2 ^ 32, ((List.range 100).map fun i => Spec.coeffNat i * x ^ i).sum % P)

def main : IO UInt32 := do
  let mut ok := true
  for x in [0, 5, 123456789, P] do
    match run 6000 (s0 (BitVec.ofNat 32 x)) with
    | none => IO.println s!"x = {x}: stuck"; ok := false
    | some s =>
      let got := ((s.getReg 10).toNat, (s.getReg 11).toNat % P)
      let good := s.pc.toNat == Image.halt && got == expected x
      IO.println s!"x = {x}: pc = {s.pc.toNat}, (a0, a1 mod P) = {got}, expected {expected x} {if good then "OK" else "MISMATCH"}"
      ok := ok && good
  return if ok then 0 else 1
