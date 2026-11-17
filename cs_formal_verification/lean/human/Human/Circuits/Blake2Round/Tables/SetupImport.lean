module
public import Human.Circuits.Blake2Round.Tables.Setup

@[expose] public section

namespace Airbender.Blake2Round

/- The row formulas of the extended-control round setup (cs/src/tables/binops.rs: `create_xor_table`,
   `create_xor_with_carry_table`, `create_xor_4x3_table`) and the claim that the imported rows are these formulas. The
   round table (`setupTable`) reads the imported rows; the circuit proofs use the formulas. -/

/-- Row `n` of the round setup, one formula per column, by region: the XOR tables with 8-, 7- and 9-bit keys (tags 4,
    19 and 20), the XOR tables with carry with 8- and 7-bit keys (tags 55 and 56), the split XOR table (4+3)x(4+3)
    (tag 57), then zero padding from row 606208. Columns: the two keys, the XOR (or the carry), the second output, the
    split output, the tag. -/
def formulaRow (n : Nat) : Vector Nat 6 := #v[
  (if n < 65536 then n / 256
   else if n < 81920 then (n - 65536) / 128
   else if n < 344064 then (n - 81920) / 512
   else if n < 540672 then (n - 344064) % 65536 / 256
   else if n < 589824 then (n - 540672) % 16384 / 128
   else if n < 606208 then (n - 589824) / 1024
   else 0),
  (if n < 65536 then n % 256
   else if n < 81920 then (n - 65536) % 128
   else if n < 344064 then (n - 81920) % 512
   else if n < 540672 then (n - 344064) % 256
   else if n < 589824 then (n - 540672) % 128
   else if n < 606208 then (n - 589824) / 128 % 8
   else 0),
  (if n < 65536 then n / 256 ^^^ n % 256
   else if n < 81920 then (n - 65536) / 128 ^^^ (n - 65536) % 128
   else if n < 344064 then (n - 81920) / 512 ^^^ (n - 81920) % 512
   else if n < 540672 then (n - 344064) / 65536
   else if n < 589824 then (n - 540672) / 16384
   else if n < 606208 then (n - 589824) / 8 % 16
   else 0),
  (if n < 344064 then 0
   else if n < 540672 then (n - 344064) % 65536 / 256 ^^^ (n - 344064) % 256
   else if n < 589824 then (n - 540672) % 16384 / 128 ^^^ (n - 540672) % 128
   else if n < 606208 then (n - 589824) % 8
   else 0),
  (if n < 589824 then 0
   else if n < 606208 then
     ((n - 589824) / 1024 ^^^ (n - 589824) / 8 % 16) |||
       (((n - 589824) / 128 % 8 ^^^ (n - 589824) % 8) <<< 4)
   else 0),
  (if n < 65536 then 4
   else if n < 81920 then 19
   else if n < 344064 then 20
   else if n < 540672 then 55
   else if n < 589824 then 56
   else if n < 606208 then 57
   else 0)]

/-- The imported round setup holds the formula rows on its complete trace domain. -/
def SetupImportClaim : Prop :=
  blake2RoundSetup.traceLen = 1048576 ∧ blake2RoundSetup.Rows fun n => (formulaRow n).map (fun v : Nat => (v : Int))

end Airbender.Blake2Round
