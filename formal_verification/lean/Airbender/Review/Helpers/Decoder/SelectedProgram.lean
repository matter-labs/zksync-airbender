import Airbender.Data.Decoder.SelectedProgram

/-!
The public selected pooled/unified programs are decoded from the four actual
leading words of `ROM.nativeProgramData`, imported from the retained word-memory
setup. Their constructors require successful pinned Sail decoding and preserve
the complete imported image, original instruction and family metadata.

This selected pure-decoder projection is distinct from the generalized stateful
`programEntryRunWith`/`programImageRunWith` interfaces. Those interfaces still run
original Sail on the public state, including configuration reads such as REV8's
misa dependency. This import route does not change either admission rule.
-/
