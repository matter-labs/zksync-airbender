module
public import Slop.Trace.SailHistory
public import Human.Helpers.Core.Field

@[expose] public section

namespace Tests.SailHistory
open Airbender Arithmetic Trace Reference
set_option warningAsError true

private def valueCode (value : BitVec 32) : Nat :=
  Nat.pair (Word.ofBitVec value).lo (Word.ofBitVec value).hi
private theorem value_code (value : BitVec 32) : memoryWord (valueCode value) = value := by
  simp only [memoryWord, valueCode, Nat.unpair_pair]
  change (Word.ofBitVec value).toBitVec = value
  exact Word.ofBitVec_roundtrip value
end Tests.SailHistory
