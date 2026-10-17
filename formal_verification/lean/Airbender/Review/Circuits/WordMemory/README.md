# Word-memory circuit review

## Checked result

[Theorems](Theorems.lean) prove native v2 transfer laws and bounded RV32 address
addition from the complete imported row constraints. [Model](Model.lean) lists the
observables and the exact scope.
[Artifact](Artifact.lean) imports every native equation and query; all calculations
stay in [Proofs](../../../Proofs/WordMemory/Transfers.lean).

The native mask is Boolean. Mixed ports select rs2 or the effective RAM address
on reads, and rd or the effective RAM address on writes. The complete native ROM
lookup enforces four-byte alignment on every path. RAM loads copy the read port;
ROM loads select the public ROM word. Both use the actual decoder-owned x0 mask.
Stores require the RAM region and copy the second port into the actual write.

| Observable | Native logical variable IDs |
| --- | --- |
| Initial/final PC and clocks | 0,1 / 13,14 and 2,3 / 15,16 |
| rs1/rs2/rd, x0 flag, immediate, funct3, store mask | 5 / 6 / 7 / 8 / 9,10 / 11 / 12 |
| rs1 value / effective address | 17,18 / 19,20 |
| RAM flag / ROM high-address chunk | 22 / 23 |
| ROM data | 26,27 |
| Mixed read address / value | 28,29 / 30,31 |
| Mixed write register flag / address / prior value / actual value | 32 / 33,34 / 35,36 / 37,38 |

[ROM tables](../../Helpers/Tables/WordROM.lean) retain all 65536 separator rows
and all 1048576 aligned ROM rows. Missing public words retain native 0xc0001073
UNIMP padding. Neither lookup is conditional: even a RAM access queries its ROM
shadow address. ROM loads also retain the native readonly RAM port; its discarded
read remains a history obligation. These definitions model the pinned native
four-MiB profile; physical setup export and public Sail-byte binding remain open.

[Regressions](../../../../Tests/WordMemory.lean) instantiate full native RAM loads,
RAM stores and ROM loads, including masked x0 loads and UNIMP padding. Changed ROM
reads, unaligned addresses and ROM stores are rejected. The importer rejects
unknown/dynamic table selectors, malformed query arities and unmapped columns.

The [address calculation](../../../Proofs/WordMemory/Address.lean) uses the native
Mersenne31 carry encoding and derives both carries and actual ranged output.
Only canonical source/immediate bounds remain explicit. The
[PC proof](../../../Proofs/WordMemory/PC.lean) preserves RV32 rollover under initial
bounds/alignment. The [clock proof](../../../Proofs/WordMemory/Timestamp.lean)
derives four-tick advancement and strict port order under the shared initial/prior
clock inputs. These inputs must still come from initialized word-memory history.
Regressions read a non-padding public ROM word, derive native port order and
simultaneously wrap the address and PC from 0xfffffffc to zero.

## Next connection

This is a native row checkpoint. Public LW/SW decoding, original Sail byte binding
for the public ROM words, initialized reads/bounds (including discarded ROM-shadow
accesses) and original Sail load/store execution remain to be connected. The
native x0 flag
is visible in the load formula; its relation to rd is a decoder obligation.
The arithmetic-only trace registry remains unchanged until those connections
are proved. See the [plan](../../../../FORMAL_VERIFICATION_PLAN.md) and
[trust boundaries](../../../../TRUST_AND_REVIEW.md).
