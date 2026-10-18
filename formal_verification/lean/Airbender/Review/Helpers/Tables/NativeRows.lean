import Airbender.Proofs.Tables.NativeRows

namespace Airbender.Verification.NativeSetup

/-- Full-row scalar queries recover their canonical native ranges. -/
theorem native_row_scalar (kind : DecoderKind) (rom : WordROM) (scalar : ScalarKind)
    (value : ZMod mersenne31Modulus) :
    ColumnLookup kind rom (scalarColumn kind scalar) #v[value] ↔ value.val < 2 ^ scalar.bits :=
  Proofs.column_scalar_lookup kind rom scalar value

/-- Full-row decoder queries at imported placement recover actual native data. -/
theorem native_row_decoder (kind : DecoderKind) (rom : WordROM)
    (query : Vector (ZMod mersenne31Modulus) 10) :
    ColumnLookup kind rom kind.columns.decoderStart query ↔
      ∃ i : Fin 1048576, query = decoderPrefixRow kind i :=
  Proofs.column_decoder_data kind rom query

/-- Full-row generic membership preserves the native table tag and group count. -/
theorem native_row_tagged (kind : DecoderKind) (rom : WordROM) (tag : Nat)
    (query : Vector (ZMod mersenne31Modulus) 3) :
    TaggedLookup kind rom tag query ↔ kind.columns.genericGroups = 1 ∧ Contains rom tag query :=
  Proofs.column_tagged_lookup kind rom tag query

end Airbender.Verification.NativeSetup
