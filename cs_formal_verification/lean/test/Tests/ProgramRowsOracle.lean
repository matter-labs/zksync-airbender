import Proven.Compiler.ExecutableDecoder

open Airbender Airbender.Trace Airbender.Compiler.NativePublicSetup

private def parseFamily : String → Option PooledFamily
  | "add-sub" => some .addSub
  | "jump-branch" => some .jumpBranchSlt
  | "shift-binop" => some .shiftBinop
  | "word-memory" => some .wordMemory
  | "subword-memory" => some .subwordMemory
  | "mul-div" => some .mulDiv
  | _ => none

/-- Emit logical fields and their native payload. `rows_decoder_binding` proves that the payload
    is the decoder region of `NativePublicSetup.rows`. The checker validates all sentinel slots. -/
def main (args : List String) : IO Unit := do
  let [config, familyName, input, output] := args
    | throw (IO.userError "usage: program_rows_oracle full|reduced|unified FAMILY TEXT.bin OUTPUT.csv")
  unless config == "full" || config == "reduced" || config == "unified" do
    throw (IO.userError "Unknown decoder configuration")
  let bytes ← IO.FS.readBinFile input
  unless bytes.size % 4 == 0 do
    throw (IO.userError "The public text must contain complete words")
  let profile := if config == "full" then RVMachineConfig.unrolledFullUnsigned
    else if config == "reduced" then .unrolledReduced else .unified
  let selected ← if config == "unified" then do
    unless familyName == "unified" do throw (IO.userError "Expected the unified family")
    pure RVMachineDecoderFamily.unified
  else do
    let some family := parseFamily familyName | throw (IO.userError "Unknown decoder family")
    pure (RVMachineDecoderFamily.pooled family)
  let initial : RV.State := {
    pc := 0, regFile := fun _ => 0, mem := fun _ => 0
    rom := fun address => BitVec.ofNat 8 (bytes[address.toNat]?.getD 0).toNat }
  let addresses := (List.range (bytes.size / 4)).map (fun index => BitVec.ofNat 32 (4 * index))
  let some program := rvMachineProgramImage profile initial addresses
    | throw (IO.userError "Public program construction failed")
  let addressIndex := rvMachineProgramIndex program
  let slot := fun index => addressIndex[4 * index]?
  IO.FS.withFile output .write fun handle => do
    for index in [:bytes.size / 4] do
      let some entry := slot index | continue
      unless entry.data.family == selected do continue
      let values := (entry.data.row entry.pc).toList ++ decoderRowNatWith selected slot index
      handle.putStrLn (String.intercalate "," (toString index :: values.map toString))
