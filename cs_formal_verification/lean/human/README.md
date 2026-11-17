# Reviewed specification

This directory contains the reviewed statements of the Airbender verification.
The trusted base is the Lean kernel, the standard axioms, the official Sail model,
and the definitions and claims stated here. The proofs are in `proven/`.

Two libraries form the specification:

- [Human](Human/README.md) contains the ISA, circuit, helper, trace, compiler and import definitions.
- [CleanCore](CleanCore/README.md) contains our transcription of the Clean definitions used by the claims.

The import rule permits Lean, Mathlib and this directory. The official Sail model
is an explicit input to [ISA/Sail](Human/ISA/Sail/README.md) and
[Configuration.lean](Human/Helpers/Core/Configuration.lean).
[CleanCore/Equivalence.lean](CleanCore/Equivalence.lean) is the only module that
imports Clean. No module imports it. The
[import closure check](../scripts/check_import_closure.py) checks this boundary.

Read the [results table](Human/README.md) and the
[claim inventory](../../docs/VERIFICATION_STATUS.md) first. Then read the
[ISA](Human/ISA/RV32.lean), [circuits](Human/Circuits/README.md),
[traces](Human/Trace/README.md) and [compiler](Human/Compiler/README.md) guides.
The root README has the [file map](../../README.md#layout).

These modules perform trusted import or comparison operations:

- [Transcribe.lean](Human/Import/Transcribe.lean) composes the JSON parser and circuit decoder.
- [TranscribeCommand.lean](Human/Import/TranscribeCommand.lean) reads circuit files and runs the import command.
- [SetupEmit.lean](Human/Import/SetupEmit.lean) reads compressed setup data and emits setup terms.
- [NativeGrid.lean](Human/Import/NativeGrid.lean) compares the subword and unified fixed rows with native JSON rows in compiled code.

The [trust lists](Human/Trust.lean) name the allowed external roots and tactic modules.
The [import guide](Human/Import/README.md) states the parser, decoder and placement
claims. The [trust guide](../../docs/TRUST_AND_REVIEW.md) states the checks and the
limits of the trusted operations. Read each claim with its public data and
interface premises.
