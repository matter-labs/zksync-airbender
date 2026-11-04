# Modular pooled execution

[Theorems](Theorems.lean) proves complete six-family execution including
ADDMOD/SUBMOD/MULMOD/FMAMOD, with terminal PC and tracked-cell agreement.
Native boot/ROM and the existing external padding boundary are supported.
[ExternalTheorems](ExternalTheorems.lean) combines the same operations with
external reads and write hints, consuming exactly the independent stream
responses selected by native read ports. Authentication stays external.

[ExternalCalls](ExternalCalls.lean) adds complete standard delegated caller
retirement to this stream relation. The proved
[reduced target](../../../Proofs/Reduced/MachineTarget.lean) composes it with the
four CPU families and extended-round workers. The proved
[full unsigned target](../../../Proofs/FullUnsigned/Target.lean) uses
[FullUnsigned](../FullUnsigned.lean), which also includes the three blessed split
Keccak worker circuits and their 361-call wrapper.

[ReducedUse](ReducedUse.lean) states the public extended-round wrapper shape,
entry and argument premises for every external stream. Native execution under
those premises is proved. The native target corollaries certify CPU rows only;
worker flat equations, exact matching and the submitted instance roster remain
premises. Each target currently has one initialization/teardown instance.
Reduced `workerFamilies` requires every submitted worker to be extended round;
other standard workers and all split pools are assumed absent.

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
old-destination reads, wrong selectors and unsupported MOPs. The combined
fixture checks dependent reads→modular arithmetic→hint→ADD execution and rejects
short or reordered streams.

[Unified execution](../UnifiedReduced/ModularExecution.lean) connects these four
operations to the unified artifact alongside standard instructions, TRIADD and
XORROT, with the same public boot and external padding contracts.
