# GKR compiler semantic preservation

<!-- source-names: keccak_special5 -->

For human review, start with the [compiler entrypoints and their definitions](Airbender/Review/Compiler/README.md).
Readers and capture bindings are under `Airbender/Import`; supporting calculations
and generated certificates are under `Airbender/Proofs`. This guide records
current scope and validation limits. The
[historical record](GKR_COMPILER_VERIFICATION_HISTORY.md) retains detailed
implementation stages, intermediate APIs and checkpoint evidence.

## Current scope and validation limits

The restored hash circuits have known gaps covered by the explicit
[F11 hash witness contracts](FINDINGS.md#f11--hash-witness-contracts-remain-unenforced).
Those are private-witness assumptions, not native enforcement or public-input
validation. Circuits are unchanged to make proofs succeed.
The [supported-use trace entrypoint](Airbender/Review/Trace/UnifiedReduced/SupportedUseExecution.lean)
instead derives the bigint/hash worker contracts from public program safety and
exact native prefixes for bigint, G and extended round. This does not enlarge the
captured compiler/program registry or establish split-Keccak coverage.

The Keccak captures and execution lemmas cover `keccak_special5`, whose complete
protocol has 649 calls. The provided Keccak wrapper instead uses 361 calls to
three split circuits with no current Lean coverage; the inspected unified setup
also omits their CSRs. Those captures therefore do not establish compiler or
execution coverage for the blessed Keccak path. Split modeling and integration
are deferred; [F12](FINDINGS.md#f12--blessed-keccak-path-is-outside-current-proof-coverage)
records the agreed scope.

For 22 captured cached/uncached compilations, base-field arithmetic preservation
is proved. Wiring/cache checks, 60 lookup-output reductions and 48 RAM-product
reductions are supporting results. New physical-row logical execution entrypoints
use only the actual physical assignment, native base-field arithmetic and an
active row, plus exact native lookup-tuple matching. Native requests are built
from consumed native encoding fields and leaf weights at the physical assignment.
Checked field/mask/helper identities under full native arithmetic transport them
to source operands; native operand coverage and independent setup-column bindings
connect primitive/group/setup selection. Their composition derives authored
membership, helper bounds, Clean validity and decoder membership without canonical
source/borrow framing. Exact state/RAM permutations and public
boundaries/seed remain explicit. Older framed entrypoints remain compatible.

The [logical lookup argument](Airbender/Review/Compiler/LookupArgument.lean)
uses natural multiplicities. The remaining final compressed/sampled
sum-to-exact-matching step is not proved, and those multiplicities are not tied to
physical field counters. [Supplied-program boundaries](Airbender/Review/Compiler/Program.lean)
require structural decoder-table equality with the retained capture and the
existing public execution inputs. This supports compatible supplied programs,
not arbitrary new programs/setups. The retained-program wrapper still uses its
four-entry fixture. Explicit Airbender-platform wrappers select that device
configuration; generic wrappers remain polymorphic. Generic source/trace execution
already supports arbitrary programs under its stated contracts. See the
[execution premise table](Airbender/Review/Compiler/README.md#execution-premises).

All 14 actual native logical-row compositions compile, covering payload/mask/helper
transport, operand coverage and setup bindings. Program execution, logical
execution and the final public theorem module compile and pass selected-module
kernel replay with a 32 MiB Lean thread stack. The final selected frontend also
passes over 3279 modules, including 10 concrete Tests and five retained Sail
modules, with normal Lake no-build freshness and compiled artifact-hash checks
without repairs. Its source/compiled manifests bind only that selected scope;
no full assurance build snapshot was issued.

The full compiler checkpoint, environment dependency audit and independent replay
have not completed at the current head. Recorded post-rollback checks covered
293 regenerated compiler modules and focused direct axiom reports; those reports
are smoke tests and can under-report imported constructor-type dependencies.
They do not establish a full standard-axiom dependency audit.

## Arithmetic extension and logical arguments

The [arithmetic claims](Airbender/Review/Compiler/Theorems.lean) distinguish
backward preservation from witness extension. Preservation derives every original
source arithmetic assertion from the whole captured native base-field relation.
Extension constructs an assignment satisfying only a certificate-selected native
arithmetic gate slice. The certificate is untrusted and Lean checks its selected
identities; it does not prove the slice covers every source-related emitted gate
or construct a witness for the complete GKR graph.

Standalone wiring, lookup-output and RAM-product reductions do not by themselves
turn balanced sampled sums/products into exact membership or token permutations.
Those logical-argument and public-boundary conditions remain visible in the
[compiler contracts](Airbender/Review/Compiler/README.md#execution-premises).
Universal correctness of the Rust compiler, cryptographic enforcement and
whole-system completeness remain outside these captured-instance results.

## Evidence and reproduction

Current native Rust capture regeneration and both retained/fresh production
checks pass: all 67 files reproduce byte for byte. The measured guarded run took
27.06 seconds, with peak footprint 1341.22 MiB and resident memory 1353.02 MiB,
and left no surviving owned workers. This is native capture/provenance evidence;
it is separate from the focused Lean build/replay results above. The final public
wrapper build took 37.49 seconds, with peak footprint 586.75 MiB and resident
memory 3093.56 MiB, and left no surviving owned workers. The final one-worker
selected frontend took 96.51 seconds, with peak footprint 538.71 MiB and resident
memory 1585.52 MiB, and left no surviving owned workers. Upstream platform
compatibility also compiles in the current source.

The full project frontend, executable/runtime checks, full environment audit,
complete independent dependency replay, transitive negative controls and Linux/
cold-run feasibility remain pending. The 25 native setup freshness jobs/receipts
are a separate gate from the 67-file compiler capture reproduction.

The setup-input dependency control passes eight dirty cases using an isolated
fixture with the actual Lake target metadata: two inputs across four setup-reading
test modules. It checks dependency wiring, not those modules' actual test bodies.
The actual four setup tests also compile and are included in the final selected
frontend, alongside the three previously omitted GKR tests, two new regressions
and upstream platform compatibility.

Use [verification status](VERIFICATION_STATUS.md) for completed evidence and
pending gates, and [reproduction](README.md#reproduce) for current commands. The
maintained native-request generator has a reproduction check there.
The [historical compiler record](GKR_COMPILER_VERIFICATION_HISTORY.md) preserves
dated checkpoint counts; its old declaration names and passing stages do not
establish current APIs or a current-head pass.
