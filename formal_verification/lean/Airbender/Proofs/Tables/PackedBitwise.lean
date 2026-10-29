import Airbender.Proofs.Tables.PackedBytes

namespace Airbender.Setup.Proofs.PackedBitwise
open Airbender.Setup.Proofs.PackedBytes
set_option warningAsError true
-- `simp` on the 256-byte replication proof needs deeper recursion; the
-- generic checker and every capture-specific `ok` use default heartbeats.
set_option maxRecDepth 131072

def indexPacked : Nat := 0xfffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0dfdedddcdbdad9d8d7d6d5d4d3d2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100
def repeatedOnes : Nat := 0x1010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101

/-- Kernel-checked constants used for all three 256-by-256 bytewise tables. -/
theorem index_correct : indexPacked = Nat.ofDigits 256 (List.range 256) := by decide +kernel
theorem ones_correct : repeatedOnes = Nat.ofDigits 256 (List.replicate 256 1) := by decide +kernel

theorem index_byte (column : Nat) (hc : column < 256) :
    (indexPacked / 256 ^ column) % 256 = column := by
  rw [index_correct, extractDigit]
  · simp [hc]
  · intro digit hd
    exact List.mem_range.mp hd
  · simpa using hc

theorem repeated_byte (row column : Nat) (hr : row < 256) (hc : column < 256) :
    ((row * repeatedOnes) / 256 ^ column) % 256 = row := by
  rw [ones_correct, Nat.mul_ofDigits]
  simp only [List.map_replicate, mul_one]
  rw [extractDigit]
  · exact List.getElem_replicate (by simpa using hc)
  · intro digit hd
    exact (List.eq_of_mem_replicate hd).symm ▸ hr

inductive Operation where
  | bitAnd | bitOr | bitXor
  deriving DecidableEq

def Operation.apply : Operation → Nat → Nat → Nat
  | .bitAnd => Nat.land
  | .bitOr => Nat.lor
  | .bitXor => Nat.xor

def expectedRow (operation : Operation) (row : Nat) : Nat :=
  operation.apply indexPacked (row * repeatedOnes)

def check (operation : Operation) (data : Array Nat) : Bool :=
  checkRows data 256 (expectedRow operation)

def Fact (operation : Operation) (data : Array Nat) : Prop :=
  ∀ row column, row < 256 → column < 256 →
    (data[row]?.map fun packed => (packed / 256 ^ column) % 256) =
      some (operation.apply row column)

theorem expected_byte (operation : Operation) (row column : Nat)
    (hr : row < 256) (hc : column < 256) :
    (expectedRow operation row / 256 ^ column) % 256 =
      operation.apply row column := by
  cases operation with
  | bitAnd =>
    change ((indexPacked &&& (row * repeatedOnes)) / 256 ^ column) % 256 = row &&& column
    rw [extractAnd, index_byte column hc, repeated_byte row column hr hc, Nat.and_comm]
  | bitOr =>
    change ((indexPacked ||| (row * repeatedOnes)) / 256 ^ column) % 256 = row ||| column
    rw [extractOr, index_byte column hc, repeated_byte row column hr hc, Nat.or_comm]
  | bitXor =>
    change ((indexPacked ^^^ (row * repeatedOnes)) / 256 ^ column) % 256 = row ^^^ column
    rw [extractXor, index_byte column hc, repeated_byte row column hr hc, Nat.xor_comm]

/-- The checked packed rows entail each of the 65,536 byte equations for any
of the three bitwise tables. The proof is independent of imported data. -/
theorem check_sound (operation : Operation) (data : Array Nat)
    (h : check operation data = true) : Fact operation data := by
  intro row column hr hc
  have hrow := checkRows_sound data 256 (expectedRow operation) h ⟨row, hr⟩
  rw [hrow]
  exact congrArg some (expected_byte operation row column hr hc)

end Airbender.Setup.Proofs.PackedBitwise
