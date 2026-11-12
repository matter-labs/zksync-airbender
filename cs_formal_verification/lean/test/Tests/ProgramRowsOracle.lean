import Human.Helpers.Decoder.RVPooledProgram
import Human.Helpers.UnifiedReduced.RVProgram

open Airbender Airbender.Trace

private def parseFamily : String → Option PooledFamily
  | "add-sub" => some .addSub
  | "jump-branch" => some .jumpBranchSlt
  | "shift-binop" => some .shiftBinop
  | "word-memory" => some .wordMemory
  | "subword-memory" => some .subwordMemory
  | "mul-div" => some .mulDiv
  | _ => none

private def wordAt (bytes : ByteArray) (index : Nat) : BitVec 32 :=
  BitVec.ofNat 32 <|
    (bytes[4 * index]?.getD 0).toNat +
    256 * (bytes[4 * index + 1]?.getD 0).toNat +
    65536 * (bytes[4 * index + 2]?.getD 0).toNat +
    16777216 * (bytes[4 * index + 3]?.getD 0).toNat

private def row {Kind : Type} (index : Nat) (data : DecoderData Kind) : List Nat :=
  [4 * index % 65536, 4 * index / 65536, data.rs1.toNat, data.rs2.toNat, data.rd.toNat,
    data.immediate.lo, data.immediate.hi, data.funct3, data.mask]

/-- Emit the active rows of the reviewed RV decoder projections. The checker validates all other native rows. -/
def main (args : List String) : IO Unit := do
  let [config, familyName, input, output] := args
    | throw (IO.userError "usage: program_rows_oracle full|reduced|unified FAMILY TEXT.bin OUTPUT.csv")
  unless config == "full" || config == "reduced" || config == "unified" do
    throw (IO.userError "Unknown decoder configuration")
  let bytes ← IO.FS.readBinFile input
  unless bytes.size % 4 == 0 do
    throw (IO.userError "The public text must contain complete words")
  IO.FS.withFile output .write fun handle => do
    for index in [:bytes.size / 4] do
      let some instruction := RV.decode (wordAt bytes index) | continue
      let values ← if config == "unified" then do
        unless familyName == "unified" do throw (IO.userError "Expected the unified family")
        pure ((UnifiedReduced.rvDecoderFields instruction).map (row index))
      else do
        let some family := parseFamily familyName | throw (IO.userError "Unknown decoder family")
        pure ((rvPooledDecoderFields instruction).filter (·.family == family) |>.map (row index))
      if let some values := values then
        handle.putStrLn (String.intercalate "," (toString index :: values.map toString))
