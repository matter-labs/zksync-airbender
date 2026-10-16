import Human.RV32
import Human.Spec
import Human.SpecBlake
import Human.Delegations
import Image
import ImageMop
open RV

/-! Sanity check of human/RV32 (compiled, not a proof): run both images concretely from address 0 for a few inputs
and compare the outputs with a direct computation. Prints one line per run and exits 1 on a mismatch. -/

def P : Nat := 2 ^ 31 - 1
def p : Nat := BabyBearP

/-- Memory: the image (zero elsewhere). -/
def mem0 (bytes : Array (BitVec 8)) : Word → BitVec 8 := fun a =>
  if h : a.toNat < bytes.size then bytes[a.toNat] else 0

/-- Ext4 product on limbs `(c0.c0, c0.c1, c1.c0, c1.c1)` (`w⁴ = 11`, the table of `ext4.rs`). -/
def mul4 (a b : List Nat) : List Nat :=
  let g := fun i => a.getD i 0
  let h := fun i => b.getD i 0
  [(g 0 * h 0 + 11 * (g 1 * h 1 + g 2 * h 3 + g 3 * h 2)) % p,
   (g 0 * h 1 + g 1 * h 0 + g 2 * h 2 + 11 * (g 3 * h 3)) % p,
   (g 0 * h 2 + 11 * (g 1 * h 3) + g 2 * h 0 + 11 * (g 3 * h 1)) % p,
   (g 0 * h 3 + g 1 * h 2 + g 2 * h 1 + g 3 * h 0) % p]

def add4 (a b : List Nat) : List Nat := (a.zip b).map fun (x, y) => (x + y) % p

/-- `∑_{i < 32} cᵢ yⁱ`, `cᵢ = (i + 1, 2 i + 3, i², 7)`, by Horner. -/
def poly4 (y : List Nat) : List Nat :=
  (List.range 32).reverse.foldl (fun acc i => add4 (mul4 acc y) [i + 1, 2 * i + 3, i ^ 2, 7]) [0, 0, 0, 0]

/-- Blake2s (7 rounds) of the five input words: the first two digest words. -/
def blake2 (x : Nat) (y : List Nat) : List Nat :=
  let d := Spec.blake5 #v[BitVec.ofNat 32 x, BitVec.ofNat 32 y[0]!, BitVec.ofNat 32 y[1]!, BitVec.ofNat 32 y[2]!,
    BitVec.ofNat 32 y[3]!]
  [d[0].toNat, d[1].toNat]

def expected (x : Nat) (y : List Nat) : List Nat :=
  [(3 * x + 1) % 2 ^ 32, ((List.range 100).map fun i => Spec.coeffNat i * x ^ i).sum % P] ++ poly4 y ++ blake2 x y

/-- The memory a run touches (the stack top, the copied `.rodata`, `.bss`) as an array, so that a long run does
not pile up `write` closures (test code only: the steps themselves are `RV.step`). -/
def lo : Nat := 0x13ff800
def hi : Nat := 0x1401200
def window (m : Word → BitVec 8) : Array (BitVec 8) :=
  (Array.range (hi - lo)).map fun i =>
    if lo + i < 0x1400400 ∨ 0x1401000 ≤ lo + i then m (BitVec.ofNat 32 (lo + i)) else 0

/-- `RV.run` in chunks of 100 steps (until `halt`), flattening registers and memory in between. -/
def runFlat (base : Word → BitVec 8) (k : Nat) (s : State) (halt : Nat) : IO (Option State) := do
  let mut s := s
  for c in [0:k] do
    if s.pc.toNat = halt then break
    match run 100 s with
    | none => return none
    | some s' =>
      let regs : Array Word := (Array.range 32).map fun i => s'.regFile (BitVec.ofNat 5 i)
      let arr ← IO.lazyPure fun _ => window s'.mem
      if arr.size = 0 then return none
      s := { s' with mem := fun a => if lo ≤ a.toNat ∧ a.toNat < hi then arr[a.toNat - lo]! else base a,
                     regFile := fun i => regs[i.toNat]! }
      if (← IO.getEnv "RUN_DEBUG").isSome then IO.eprintln s!"chunk {c} pc {s.pc.toNat}"
  return some s

def runOne (name : String) (bytes : Array (BitVec 8)) (halt : Nat) (x : Nat) (y : List Nat) : IO Bool := do
  let base := mem0 bytes
  let s0 : State := { pc := 0, regFile := fun _ => 0, mem := base, input := (x :: y).map (BitVec.ofNat 32 ·) }
  match ← runFlat base 2000 s0 halt with
  | none => IO.println s!"{name} x = {x}, y = {y}: stuck"; return false
  | some s =>
    let got := [(s.getReg 10).toNat, (s.getReg 11).toNat % P, (s.getReg 12).toNat, (s.getReg 13).toNat,
      (s.getReg 14).toNat, (s.getReg 15).toNat, (s.getReg 16).toNat, (s.getReg 17).toNat]
    let good := s.pc.toNat == halt && got == expected x y
    IO.println s!"{name} x = {x}, y = {y}: pc = {s.pc.toNat}, outputs {got}, expected {expected x y} {if good then "OK" else "MISMATCH"}"
    return good

/-- Airbender's Blake2s delegation (7 rounds, normal mode) on one last block of the five words `w`, laid out as
`blake2s_u32` does (state, extended state with the counter and last-block words, input at `+128`): the digest. -/
def delegationDigest (w : List Nat) : List Nat :=
  let ws : List Word := (List.ofFn fun i : Fin 8 => Spec.configuredIV i) ++
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20 ^^^ Spec.IV 4, 0, 0xFFFFFFFF ^^^ Spec.IV 6, 0] ++ List.replicate 8 0 ++
    w.map (BitVec.ofNat 32 ·) ++ List.replicate 11 0
  let mem : Word → BitVec 8 := fun a =>
    if 0x1401000 ≤ a.toNat ∧ a.toNat < 0x1401000 + 4 * ws.length then
      (ws.getD ((a.toNat - 0x1401000) / 4) 0 >>> (8 * (a.toNat % 4))).setWidth 8 else 0
  match Delegation.blake2s 0x1401000 0x1401080 ((0b1001 : Word) <<< 16) mem with
  | some (_, _, out) => (out.toList.take 8).map (·.toNat)
  | none => []

def main : IO UInt32 := do
  let mut ok := true
  for (x, y) in [(5, [1, 2, 3, 4]), (123456789, [p - 1, 7, 0, 1234567])] do
    let d := delegationDigest (x :: y)
    let e := ((Spec.blake5 #v[BitVec.ofNat 32 x, BitVec.ofNat 32 y[0]!, BitVec.ofNat 32 y[1]!, BitVec.ofNat 32 y[2]!,
      BitVec.ofNat 32 y[3]!]).toList).map (·.toNat)
    let good := d == e
    IO.println s!"delegation 0x7c7, x = {x}, y = {y}: {d.take 2} vs blake5 {e.take 2} {if good then "OK" else "MISMATCH"}"
    ok := good && ok
  for (x, y) in [(0, [0, 0, 0, 0]), (5, [1, 2, 3, 4]), (123456789, [p - 1, 7, 0, 1234567]), (P, [5, p - 2, 11, 0])] do
    ok := (← runOne "app    " Image.bytes Image.halt x y) && ok
    ok := (← runOne "app_mop" ImageMop.bytes ImageMop.halt x y) && ok
  return if ok then 0 else 1
