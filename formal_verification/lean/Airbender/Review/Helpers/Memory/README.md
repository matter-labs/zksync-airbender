# Native memory and initialized history

This directory models native register/RAM transfers with their addresses, values
and retained timestamps, starting from an independent public Sail image. Its
history relations connect those transfers to actual Sail states. Native zero ROM
shadows and public ROM bytes remain separate representations, linked only where a
claim supplies the required view conversion.

Start with [InitialImage](InitialImage.lean) for actual public Sail GPR/byte reads
and the tracked cell domain. [Initialization](Initialization.lean) describes the
boot profile; [Platform](Platform.lean) records the ordinary-memory configuration.

[Ports](Ports.lean) and [IndirectPorts](IndirectPorts.lean) interpret imported
addresses, timestamps and values. [Values](Values.lean) gives the word view.
[History](History.lean) states logical native events and matching; its rows and
tokens come from the shared [model](../Context/Model.lean).

[SailHistory](SailHistory.lean) connects those transfers to actual Sail states.
Bounds and latest-write reads are derived by the supporting proofs from accepted
constraints, preserved writes and public initialization; desired reads are not supplied.

[ROM](ROM.lean) models public word-ROM tables. [Native](Native.lean) keeps the
prover's zero ROM shadows separate from actual public bytes and names the view conversion.
Check the claim's tracked domain, alignment, platform, seed timestamps and terminal tokens.

Logical matching is explicit; this is not a cryptographic memory-argument proof.
The checked [worker ROM boundary](../../../../Tests/DelegationROMBoundary.lean)
prevents silently replacing worker shadows with public bytes.
Whole-run terminal realization belongs in [Trace](../../Trace/README.md).
