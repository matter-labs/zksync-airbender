# Cached circuit captures

The seven CPU, four standard-worker and three split-worker modules state cached
description equality, arithmetic preservation and arithmetic witness claims. Start with
[AddSub.lean](AddSub.lean), then read the module for the circuit under review.
The [compiler guide](../README.md) lists the interfaces and machine targets.

Description claims bind the constraint sections to the family artifact.
Arithmetic claims take native gates and placement agreement as premises.
[Worker certificates](../WorkerCertificates.lean) also bind native lookups and the
participation flag for the six worker circuits used by the machine targets.
Memory matching is an explicit interface. The
[import guide](../../Import/README.md) states the trusted transcription boundary.
