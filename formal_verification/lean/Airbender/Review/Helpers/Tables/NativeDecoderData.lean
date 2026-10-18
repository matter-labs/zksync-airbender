import Airbender.Review.Helpers.Tables.PhysicalSetup
import Airbender.Review.Circuits.AddSub.Tables.NativeSetupData
import Airbender.Review.Circuits.WordMemory.Tables.NativeSetupData
import Airbender.Review.Circuits.WordMemory.Tables.NativeSparseData

namespace Airbender.Verification.NativeSetup

import_native_decoder_padding decoderPadding from "artifacts/setup/decoder-padding-native.json"

/-- The three actual native decoder exports already certified regionally. -/
inductive DecoderKind where
  | arithmetic
  | wordMemory
  | wordMemoryHoles
  deriving DecidableEq

def decoderPrefixRow (kind : DecoderKind) (i : Fin 1048576) : Vector (ZMod mersenne31Modulus) 10 :=
  match kind with
  | .arithmetic => AddSub.NativeSetup.arithmeticDecoder.row i
  | .wordMemory => WordMemory.Native.exportedDecoder.row i
  | .wordMemoryHoles => WordMemory.NativeSparse.holesDecoder.row i

/-- Source-shaped active setup: actual native prefix followed by the actual
    native padding API row. The reserved normalization row is excluded by Row.
    Rust trace/normalization/LDE refinement remains separate. -/
def decoderRow (kind : DecoderKind) (row : Row) : Vector (ZMod mersenne31Modulus) 10 :=
  if h : row.val < 1048576 then decoderPrefixRow kind ⟨row.val, h⟩
  else decoderPadding.map Nat.cast

def DecoderContains (kind : DecoderKind) (query : Vector (ZMod mersenne31Modulus) 10) : Prop :=
  ∃ row : Row, query = decoderRow kind row

end Airbender.Verification.NativeSetup
