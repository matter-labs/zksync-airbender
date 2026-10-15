# Modular pooled execution

[Theorems](Theorems.lean) proves complete six-family execution including
ADDMOD/SUBMOD/MULMOD/FMAMOD, with terminal PC and tracked-cell agreement.
Native boot/ROM and the existing external padding boundary are supported.

[Public decoding](../../Helpers/Decoder/ModularProgram.lean) reads actual bytes
through pinned Sail decoding, then maps MOP.RR.0–3 to the original ADD/SUB
artifact's selector bits 3–6. Discarded writes retain ADD/NOP preprocessing.
[Execution](../Modular.lean) uses the [existing project arithmetic](../../Circuits/AddSub/Modular.lean):
canonical BabyBear results, with Montgomery radix 2^32 for multiplication/FMA.
Standard clauses remain original Sail.

[Pooled inputs](../../Helpers/Context/PooledBoundary.lean) are unchanged apart
from selecting this decoder registry. Initialized matching derives every read,
bound and selector, including FMAMOD's pre-write destination under aliasing.
Modeled tables, public configuration/domain, canonical verifier closure and
artifact/cryptographic correspondence retain their published boundaries.

[Regressions](../../../../Tests/ModularTrace.lean) check a complete dependent
eleven-instruction execution, all four discarded forms and rejection of forged
old-destination reads, wrong selectors and unsupported MOPs.
