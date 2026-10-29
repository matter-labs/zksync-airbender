import Airbender.Proofs.GKRProtocol.ProgramMasks
import Airbender.Review.Helpers.Decoder.UnifiedProgramRows

open Airbender Airbender.Trace Airbender.Trace.NativeDecoder.ProgramRows
open Airbender.Trace.NativeDecoder.ProgramRows.Proofs

private def parseFamily : String → Option PooledFamily
  | "add-sub" => some .addSub
  | "jump-branch" => some .jumpBranchSlt
  | "shift-binop" => some .shiftBinop
  | "word-memory" => some .wordMemory
  | "subword-memory" => some .subwordMemory
  | "mul-div" => some .mulDiv
  | _ => none

private def parseConfig : String → Option Config
  | "full" => some .fullUnsigned
  | "reduced" => some .reduced
  | _ => none

private def wordAt (bytes : ByteArray) (index : Nat) : BitVec 32 :=
  BitVec.ofNat 32 <|
    (bytes[4 * index]?.getD 0).toNat +
    256 * (bytes[4 * index + 1]?.getD 0).toNat +
    65536 * (bytes[4 * index + 2]?.getD 0).toNat +
    16777216 * (bytes[4 * index + 3]?.getD 0).toNat

/-- Emit only non-sentinel rows of the executable Lean decoder model. The
checker separately verifies every omitted native row is the masked sentinel.
Each line is a word index followed by the selected BabyBear field values. -/
def main (args : List String) : IO Unit := do
  let [configName, familyName, input, output] := args
    | throw (IO.userError "usage: ProgramRowsOracle full|reduced|unified FAMILY TEXT.bin OUTPUT.csv")
  let bytes ← IO.FS.readBinFile input
  unless bytes.size % 4 == 0 do
    throw (IO.userError "public text must contain complete little-endian words")
  let initial : Reference.RiscV.Sail.State :=
    { (default : Reference.RiscV.Sail.State) with
      regs := (default : Reference.RiscV.Sail.State).regs.insert .misa
        (if configName == "full" then 0x40001000 else 0x40000000) }
  let (mask, rowAt) : Mask × (Nat → List (ZMod babyBearModulus)) ←
    if configName == "unified" then
      if familyName != "unified" then
        throw (IO.userError "unified configuration requires unified family")
      pure (unifiedMask, fun index =>
        maskRow unifiedMask <|
          Airbender.Trace.NativeDecoder.UnifiedProgramRows.wordRow initial
            (wordAt bytes index) index)
    else do
      let some config := parseConfig configName
        | throw (IO.userError "unknown decoder configuration")
      let some family := parseFamily familyName
        | throw (IO.userError "unknown decoder family")
      let mask := maskOfFamily family
      pure (mask, fun index =>
        maskRow mask (nativeFamilyRow config initial family (wordAt bytes index) index))
  let unsupported : List (ZMod babyBearModulus) := maskRow mask sentinel
  IO.FS.withFile output .write fun handle => do
    for index in [:bytes.size / 4] do
      let row := rowAt index
      if row != unsupported then
        handle.putStrLn <| String.intercalate "," <|
          toString index :: row.map (fun value => toString value.val)
