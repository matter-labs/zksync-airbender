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
read now participates in the checked initialized logical history. Its
architectural projection is checked by the separate
[trace theorem](../../Trace/Families/WordMemory/Projection.lean). These definitions model the pinned native
four-MiB profile. [Public ROM extraction](../../Helpers/Tables/WordROMImage.lean)
now binds native ROM data to actual Sail bytes within the extracted prefix.
Physical setup export and boot/padding/shadow-state binding remain separate.

The [native shadow theorem](Theorems.lean) now proves exact read/write value-code
equality for every imported RAM port mapped to an address below four MiB.
The [calculation](../../../Proofs/WordMemory/Shadow.lean) uses full native
constraints and port metadata: the first two ports only refresh timestamps, and
the last port targets either a register or RAM above the ROM boundary. No initial
Sail state, expected read or ROM-byte equivalence is supplied. Ordinary/x0 ROM
loads retain readonly shadow accesses; a changing RAM store cannot inhabit that
address region. Native matching still includes all refresh tokens. Architectural
shadow projection is now checked under separate public architectural/shadow
initialization, with physical boot/ROM binding still open.

[Regressions](../../../../Tests/WordMemory.lean) instantiate full native RAM loads,
RAM stores and ROM loads, including masked x0 loads and UNIMP padding. Changed ROM
reads, unaligned addresses and ROM stores are rejected. The importer rejects
unknown/dynamic table selectors, malformed query arities and unmapped columns.

The [address calculation](../../../Proofs/WordMemory/Address.lean) uses the native
Mersenne31 carry encoding and derives both carries and actual ranged output.
Canonical source/immediate bounds are explicit in this local statement; the
[initialized assembly](../../Trace/Families/WordMemory/Inputs.lean) now derives
them, incoming PC bounds/alignment and every clock input from public construction,
accepted history and full decoder membership. The
[PC proof](../../../Proofs/WordMemory/PC.lean) preserves RV32 rollover under initial
bounds/alignment. The [clock proof](../../../Proofs/WordMemory/Timestamp.lean)
derives four-tick advancement and strict port order under the shared initial/prior
clock inputs. The [initialized history instance](../../Trace/Families/WordMemory/History.lean)
now derives these clock inputs from matching and the actual public seed boundary.
Regressions read a non-padding public ROM word, derive native port order and
simultaneously wrap the address and PC from 0xfffffffc to zero.

## Next connection

[Public LW/SW decoding](../../Trace/Families/WordMemory/README.md) now derives
actual original Sail source evidence, exact x0 flags, immediate/PC bounds and
incoming alignment from complete padded membership. Native equations exclude
padding; original x0 loads and sign extension are retained.

Native ROM data now has an actual Sail-byte bridge inside an extracted public
prefix; a complete extracted four-MiB image covers every native ROM address.
Initialized logical reads and ranges now follow from public seeds, accepted
matching and decoder membership. [Actual Sail cell histories](../../Trace/Families/WordMemory/SailHistory.lean)
now realize reads/writes and intermediate states in the full supplied native cell
image. [Projected histories](../../Trace/Families/WordMemory/Projection.lean) now
omit shadow addresses from Sail while retaining full native matching and separate
public seeds. Physical padding/boot/ROM binding and original Sail instruction
execution remain open. The local load formula keeps its native x0 flag; the
separate public decoder proof now derives that flag's exact relation to rd.
The arithmetic-only trace registry remains unchanged until those connections
are proved. See the [plan](../../../../FORMAL_VERIFICATION_PLAN.md) and
[trust boundaries](../../../../TRUST_AND_REVIEW.md).
