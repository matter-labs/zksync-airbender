# MEM: Common memory relation

> Shared mutable-memory history semantics and the global state-permutation argument
> that closes the register, RAM, PC-state, initialization/teardown, and delegation
> histories. ROM contents are supplied by lookup tables, not by this argument. The
> event classes that supply tuples, their local constraints, and the proof protocol
> that establishes an individual partition product are owned by their modules.

`*` marks a provisional relation whose complete integration with RAM and the
profile-specific initialization/teardown modules remains open.

`***` marks material imported from the `ye/mb_gkr_compiler-arguments-protocols`
branch and not yet reconciled with this hierarchy. The marker is presentation only:
metadata and cross-references use the unmarked stable ID.

Legacy `ASM-MEM-001..003` and `REQ-MEM-001..006` remain owned by
[machine-old/memory.md](../machine-old/memory.md); this module does not duplicate
those IDs.

## Guarantee

The global argument compares a read multiset against a write multiset through one
random multivariate fingerprint drawn after every tuple-determining value is bound.
Under the calling relations' tuple provenance, acceptance implies the two multisets
are equal, except with the error stated in
[global-product soundness](../soundness/memory.md). PC-state closure is integrated and
the zero-valued RAM-history treatment of ROM loads is adopted. Ordinary RAM,
register, initialization/teardown, and delegation details remain partial under the
owners named in `REL-MEM-013`.

## Symbols and inputs

### Product symbols

- `E` — the challenge and product field
- `Tags ⊂ E` — injectively embedded address-space labels
- `d ∈ ℕ` — number of randomly weighted data coordinates fixed by the instance
- `e = (tag, x) ∈ Tags × E^d` — one event, with data coordinates `x`
- `R, W` — finite multisets of events in `Tags × E^d`, the read side and the write side
- <code>R</code><sub>i</sub>, <code>W</code><sub>i</sub> — partitions of the two sides,
  indexed by the declared inventory `i ∈ I`
- `⊎` denotes multiset union; comprehensions retain multiplicity
- `χ = (β, α₀, …, α_(d−1)) ∈ E^(d+1)` — the challenge vector
- <code>enc</code><sub>χ</sub><code>(e)</code> — the factor contributed by tuple `e`
- <code>P</code><sub>R</sub><code>[i]</code>,
  <code>P</code><sub>W</sub><code>[i]</code> — products of partition `i` on each side
- <code>P</code><sub>R</sub>, <code>P</code><sub>W</sub> — aggregate products over `I`
- `tag ∈ Tags` — address-space namespace of an event, per `REL-MEM-008`
- `u16 = [0, 2¹⁶)`, `u19 = [0, 2¹⁹)`, `u32 = [0, 2³²)` — limb and word domains

### PC-state symbols

- `cycles`, `PCState`, and each `cycle.text` and `cycle.timestamp` come from the
  [common execution relation](../execution/common.md)
- `PCReads`, `PCWrites` — multisets of PC-class records
- `PCRead(cycle) = (PC, PCState[cycle.timestamp], cycle.timestamp)`
- `PCWrite(cycle) = (PC, PCState[cycle.timestamp + 4], cycle.timestamp + 4)`
- `PCInitial = (PC, 0, 4)`
- `PCFinal = (PC, exit_pc, 4 + 4 · |cycles|)`

## Assumptions

None. Every obligation this module relies on is stated as a relation below; the
modules that discharge each one are named in the open boundary.

## Canonical relation tree

> All top-level relations are conjoined.
> The first group is a top-down summary. Later groups define the tuples and proof
> bindings consumed by that summary.

- **Grand-product permutation argument**

  The argument compresses every read-side and write-side tuple into one field element,
  multiplies each side, and accepts only when the products agree.

  - **\*\*\* [`REL-MEM-001`] Grand-product permutation**

    <pre>P<sub>R</sub> = P<sub>W</sub>
    <small><i>(the product of the compressed read set equals the product of the compressed write set)</i></small>
    </pre>

    `P_R` is the left-hand side and contains the read set. `P_W` is the right-hand
    side and contains the write set.

    `REL-MEM-002..007` define the challenges, compression, two products, and boundary
    contributions summarized by this equality. No nonzero-product check is required;
    zero factors are covered by [`REQ-GP-SND-002`](../soundness/memory.md).

  - **\*\*\* [`REL-MEM-002`]\* Challenge field**

    > Stub. Unresolved under `GAP-MEM-008`.

    `E` is the extension field selected by the target. To fill in: the two supported
    choices, the recursion level and proof type selecting each one, and the `|E|` each
    contributes to [`REQ-GP-SND-001`](../soundness/memory.md).

  - **\*\*\* [`REL-MEM-003`] Shared challenge vector**

    <pre>χ = (β, α₀, …, α<sub>d−1</sub>) ∈ E<sup>d+1</sup>
    χ ← transcript, after every value determining R and W is bound
    <small><i>(no tuple coordinate may depend on χ)</i></small>

    ∀ i ∈ I: the proof of (P<sub>R</sub>[i], P<sub>W</sub>[i]) uses this same χ
    <small><i>(one challenge vector per product instance)</i></small>
    </pre>

  - **\*\*\* [`REL-MEM-004`] Tuple compression**

    <pre>enc<sub>χ</sub>(e) = β + tag + Σ<sub>j=0</sub><sup>d−1</sup> α<sub>j</sub> · x[j]
                       for e = (tag, x) ∈ Tags × E<sup>d</sup>
    <small><i>(one monic linear factor per tuple)</i></small>

    factor<sub>χ</sub>(q, e) = 1 + q · (enc<sub>χ</sub>(e) − 1)
    q = 0 ⇒ factor<sub>χ</sub>(q, e) = 1
    q = 1 ⇒ factor<sub>χ</sub>(q, e) = enc<sub>χ</sub>(e)
    <small><i>(inactive physical rows contribute the multiplicative identity)</i></small>
    </pre>

    The tag namespace, data width, and coordinate order come from `REL-MEM-008` and
    are bound by `REL-MEM-014`. The tag enters additively, with no challenge
    coordinate of its own. The semantic multisets `R` and `W` contain only rows with
    `q = 1`.

  - **\*\*\* [`REL-MEM-005`] Partition read/write products (LHS/RHS)**

    <pre>P<sub>R</sub>[i] = Π<sub>e ∈ Rᵢ</sub> enc<sub>χ</sub>(e)
    P<sub>W</sub>[i] = Π<sub>e ∈ Wᵢ</sub> enc<sub>χ</sub>(e)
    <small><i>(one left/right product pair per declared partition i ∈ I)</i></small>

    Rᵢ = ∅ ⇒ P<sub>R</sub>[i] = 1
    Wᵢ = ∅ ⇒ P<sub>W</sub>[i] = 1
    <small><i>(an empty partition contributes the multiplicative identity)</i></small>
    </pre>

  - **\*\*\* [`REL-MEM-006`] Aggregate read/write products**

    <pre>R = ⊎<sub>i ∈ I</sub> Rᵢ    ∧    W = ⊎<sub>i ∈ I</sub> Wᵢ

    P<sub>R</sub> = Π<sub>i ∈ I</sub> P<sub>R</sub>[i]
    P<sub>W</sub> = Π<sub>i ∈ I</sub> P<sub>W</sub>[i]
    <small><i>(every declared left/right partition is consumed exactly once)</i></small>
    </pre>

    Accumulation starts from `(P_R, P_W) = (1, 1)`. Multiplication is associative, so
    the aggregation tree does not affect `REL-MEM-001`.

  - **\*\*\* [`REL-MEM-007`]\* Initialization and teardown contributions**

    > Stub. The profile-specific RAM contributions remain open under `GAP-MEM-004`.

    <pre>W<sub>boundary</sub> = {(Register, x, 0, init_value(x)) | x ∈ Registers}
                ⊎ W<sub>memory-init</sub> ⊎ {PCInitial}
    <small><i>(initial tuples join the write side)</i></small>

    R<sub>boundary</sub> = {(Register, x, t_final(x), final_value(x)) | x ∈ Registers}
                ⊎ R<sub>memory-final</sub> ⊎ {PCFinal}
    <small><i>(terminal tuples join the read side)</i></small>
    </pre>

    The verifier inserts the register and PC boundary tuples. The selected
    initialization/teardown profile proves `W_memory-init` and `R_memory-final`.
    These are ordinary labeled partitions in `I` and enter the products through
    `REL-MEM-005..006`.

- **Tuples by address space**

  All producers use one tuple shape. The address-space tag determines how its address,
  timestamp, and value coordinates are interpreted.

  - **\*\*\* [`REL-MEM-008`]\* Event tuple schema**

    > Stub. The schema below is the intended shape recorded from the migration backlog;
    > no coordinate is adopted until `GAP-MEM-002` closes.

    <pre>Tags = {Register ↦ 0, RAM ↦ 1, PC ↦ 2}
    e = (tag, x)     x = (a₀, a₁, t₀, t₁, v₀, v₁)     d = 6
    a₀, a₁ ∈ u16     t₀, t₁ ∈ u19     v₀, v₁ ∈ u16

    address   = a₀ + 2¹⁶ · a₁
    timestamp = t₀ + 2¹⁹ · t₁
    value     = v₀ + 2¹⁶ · v₁
    <small><i>(low-limb-first recomposition)</i></small>

    q ∈ {0, 1}     q = 1 ⇔ the physical row contributes an event
    </pre>

    Read/write orientation is carried by membership in `R` or `W`, not by a tuple
    coordinate. For this schema, `(α₀, …, α₅)` correspond in order to
    `(α_(a₀), α_(a₁), α_(t₀), α_(t₁), α_(v₀), α_(v₁))` in `REL-MEM-004`.

  - **[`REL-MEM-009`]\* RAM-space tuples, including ROM loads**

    > Stub. Ordinary RAM transition and ordering details remain under `GAP-MEM-003`.

    <pre>RAMRead(a)  = (RAM, a, t_previous, value_previous) ∈ R
    RAMWrite(a) = (RAM, a, t_current,  value_next)     ∈ W
    <small><i>(one history transition at the accessed address)</i></small>

    a &lt; 2²² ∧ data_load(a) ⇒ value_previous = value_next = 0
    <small><i>(ROM-range loads are zero-valued in the RAM history)</i></small>
    </pre>

    For a ROM-range load, the aligned-ROM lookup supplies the architectural word while
    the RAM history only advances the timestamp at `a`. A store to that range rejects.
    ROM is therefore not a separate tag or product. Its admitted initialization and
    teardown tuples use value zero under the RAM tag.

  - **[`REL-MEM-010`]\* PC-space tuples**

    <pre>PCReads  = {PCRead(cycle) | cycle ∈ cycles} ⊎ {PCFinal}
    PCWrites = {PCInitial} ⊎ {PCWrite(cycle) | cycle ∈ cycles}

    PCReads = PCWrites

    {q ∈ u32 | (PC, q, 0) ∈ PCReads ⊎ PCWrites} = ∅
    <small><i>(no PC record carries timestamp zero; initialization is separate)</i></small>
    </pre>

    Each cycle ends at `cycle.timestamp + 4`, so bounded non-wrapping timestamps make
    these records one chain from `PCInitial` to `PCFinal`.

  - **\*\*\* [`REL-MEM-011`]\* Register and delegation tuples**

    > Stub. Unresolved under `GAP-MEM-003`.

    Register reads, writes, and boundary tuples use `tag = Register`. Delegation
    invocation and fulfillment reuse that tag and place the delegation type in the
    address position. To fill in: the exact tuples, orientation, and ordering that
    close ordinary register and delegation events together.

  - **\*\*\* [`REL-MEM-012`]\* Per-address-space closure**

    > Stub. Unresolved under `GAP-MEM-003`.

    <pre>∀ tag ∈ Tags:
      ⊎ {e ∈ R | e.tag = tag}  =  ⊎ {e ∈ W | e.tag = tag}
    <small><i>(each address-space namespace closes on its own)</i></small>
    </pre>

    The owning address-space relations must also state the ordering that turns
    multiset equality into one history chain per address.

- **Binding the argument**

  The remaining relations bind the tuple sources and product outputs to one compiled
  instance and to the transcript challenge used by `REL-MEM-001`.

  - **\*\*\* [`REL-MEM-013`]\* Partition inventory**

    > Stub. Unresolved under `GAP-MEM-003`.

    | Event class | Owning module | Status |
    |---|---|---|
    | register reads and writes | `memory/registers.md` | module not yet written |
    | RAM-namespace history events | this module | `REL-MEM-009` is partial |
    | PC and machine state | this module and [../execution/common.md](../execution/common.md) | `REL-MEM-010` covers PC-state only |
    | initialization and finalization | [init-teardown-unrolled.md](init-teardown-unrolled.md), [init-teardown-unified.md](init-teardown-unified.md) | stubs |
    | delegation invocation and fulfillment | precompile carrier module | `REL-MEM-011` is a stub |

    Each `i ∈ I` is a fixed label identifying one producer family and output channel.
    Its meaning does not come from its position in an aggregation order.

  - **\*\*\* [`REL-MEM-014`]\* Instance binding**

    > Stub. Unresolved under `GAP-MEM-004`.

    The tag namespace, data width, coordinate order, and partition inventory of
    `REL-MEM-008..013` are properties of the compiled circuit and are fixed before
    proving. To fill in: the artifact fixing each field and the setup comparison
    performed for every family, including families that commit no setup.

  - **\*\*\* [`REL-MEM-015`]\* Commitment precedes challenge**

    > Stub. Unresolved under `GAP-MEM-008`.

    Every column carrying a coordinate of a tuple in `R` or `W` is committed, and its
    commitment absorbed, before `χ` is drawn. To fill in: the column inventory, the
    absorption position relative to memory caps and proof of work, and what the
    verifier recomputes.

  - **\*\*\* [`REL-MEM-016`]\* Product outputs bind to committed rows**

    > Stub. Unresolved under `GAP-MEM-005`.

    Each `(P_R[i], P_W[i])` accumulated by the verifier is the output proven for the
    labeled partition `i`, over the rows inside its commitment, under the common `χ`
    of `REL-MEM-003`. A value not bound to that proof and commitment is rejected.

- **Not yet placed**

  > Remaining relations, in the order they should be defined. Promote each into one of
  > the groups above as it is written; none of these is an ID.

  - the admitted RAM-history address set and its populated-set representation
  - ordinary RAM load/store transitions, including read/write orientation and value
    preservation or replacement
  - register file as its own class, and whether it shares the RAM address space
  - initialization and finalization events, and the coverage obligation that the union
    of initialized windows spans the whole admitted address set
  - delegation invocation and fulfillment mirror factors, and their closure inside
    the register namespace
  - ordering and timestamp rules per address-space namespace: `t_read < t_write` per
    access, and what makes the per-address version chain total
  - why the identity is a *permutation*: from multiset equality plus per-namespace
    ordering to one chain per address
  - the sorted-memory-log framing as an alternative presentation of the same relation
    (`GAP-MEM-007`)


## Derived facts

- **\*\*\* Multiset equality**

  Under the tuple constraints owned by the producing modules, and except with the
  error stated by
  [`REQ-GP-SND-001`](../soundness/memory.md), acceptance implies `R = W` as multisets
  of tuples.

- **\*\*\* Accepted product identity**

  Acceptance establishes `REL-MEM-001` from the declared products of
  `REL-MEM-005..006`. This equality is the form consumed by the full-statement
  verifier.

- **\*\*\* Rejection conditions**

  <pre>supplied labeled-pair inventory ≠ I                            ⇒ reject
  some P<sub>R</sub>[i], P<sub>W</sub>[i] proved under χ′ ≠ χ    ⇒ reject
  P<sub>R</sub> ≠ P<sub>W</sub>                                        ⇒ reject
  <small><i>(inventory, shared-challenge, and final-product failures)</i></small>
  </pre>

- **\*\*\* Aggregation is order-free**

  `REL-MEM-006` fixes the labeled pairs consumed, not their multiplication order, so
  an aggregation tree is an implementation choice. Proof serialization and transcript
  absorption may still require a separate canonical order.

- **\*\*\* Orientation is positional**

  Under `REL-MEM-008` a tuple carries no read/write coordinate, so an event class can
  only change orientation by moving between sides, which `REL-MEM-006` forbids.

## Intended contents

- RAM-history address and value domains
- the interface to table-backed ROM reads and ROM-store rejection
- ordering and timestamp rules
- initial and final architectural memory state

Current material remains in [machine-old/memory.md](../machine-old/memory.md).
## Open boundary

- **GAP-MEM-001 — Complete state-permutation integration.** Integrate register and
  RAM records, profile-specific initialization/teardown, challenge derivation, and
  aggregate product equality with the PC tuples of `REL-MEM-010`.
- **\*\*\* GAP-MEM-002 — Event encoding.** Adopt or replace the schema recorded in
  `REL-MEM-008`: the tag namespace, limb widths and recomposition order, additive tag
  placement, selector-gated inactive-row factor, the six data coordinates and seven
  challenge elements, and the delegation namespace reuse. Decide whether the schema
  lives here or in a shared `execution/event-encoding.md` imported by every event
  producer, and re-express `REL-MEM-010` in it.
- **\*\*\* GAP-MEM-003 — Partition inventory and namespace closure.** Write the owning
  modules named in `REL-MEM-013`, bind each event class's rows, orientation, and
  ordering, and state how those event classes compose into the address-space
  namespaces closed by `REL-MEM-012`. Complete ordinary RAM transitions and the
  admitted address set around the adopted zero-valued ROM-history rule of
  `REL-MEM-009`.
- **\*\*\* GAP-MEM-004 — Full-statement accumulation.** Specify, in the owning
  full-statement-verifier module: sampling one fingerprint challenge after the bound
  statement and reusing it for every participating product; the proof and output-pair
  inventory, rejecting a missing, extra, duplicated, or mislabeled pair; the
  protocol-defined serialization order independently of multiplication order;
  setup-cap and proof-cap continuity; the position of the product challenge relative to
  proof-of-work; boundary insertion per `REL-MEM-007`; executor invocation and
  fulfillment products under the selected precompile profile; the
  initialization/teardown contribution selected by each memory profile; and final
  timestamp-limb validation, retaining the confirmed implementation drift until the
  implementation conforms or the intended relation changes.
- **\*\*\* GAP-MEM-005 — Partition-product discharge.** `REL-MEM-016` is discharged by
  the layered-circuit protocol that binds each partition output to the committed
  columns and to `REL-MEM-005` under the common `χ`. That protocol is not specified in
  this branch, so the relation currently names an obligation with no owning module.
- **\*\*\* GAP-MEM-006 — Challenge serialization.** Fix the wire encoding of the
  product challenge in its owning serialization module. The recorded intent is the
  order `α_(a₀), α_(a₁), α_(t₀), α_(t₁), α_(v₀), α_(v₁), β`, each extension element
  as four base-field words in coefficient order starting at `c₀`, for `7 · 4 = 28`
  words total.
- **\*\*\* GAP-MEM-007 — Sorted-log framing and lineage.** Decide whether the memory
  instance is additionally framed as a sorted memory log over
  `(address, timestamp, operation, value)` with initial and final scans, citing
  [Thaler, Section 6.6.2](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf)
  for that framing, and whether the permutation and local-consistency lineage over
  address, value, and version from [Two Shuffles Make a
  RAM](https://eprint.iacr.org/2023/1115) is adopted for those roles only.

- **\*\*\* GAP-MEM-008 — Preprocessing, commitment order, and challenge field.**
  Complete `REL-MEM-002..003` and `REL-MEM-015`: select the challenge field, state
  which columns must be committed and absorbed before `χ` is drawn, where that
  absorption sits relative to the memory caps and any proof-of-work stage, which two
  extension fields `E` may be, and what `|E|` each contributes to the soundness bound.
  Until this closes, the causality in `REL-MEM-003` is asserted but not located.

## References

> Adopted sources for the offline-memory-checking literature. Section anchors are not
> yet pinned; see `GAP-MEM-009`.

- [Thaler, *Proofs, Arguments, and Zero-Knowledge*](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf)
  — Section 6.6.2 is already cited by `GAP-MEM-007` for the sorted-memory-log framing
  over `(address, timestamp, operation, value)` and its initial/final scans.
- [Arun, Setty, Thaler, *Jolt: SNARKs for Virtual Machines via Lookups*](https://eprint.iacr.org/2023/1217)
  (EUROCRYPT 2024) — offline memory checking by multiset fingerprinting, in the
  lineage of Blum et al. and Spice, with a timestamp stored alongside the value at
  each address. This is the closest published match to `REL-MEM-001..006` together
  with the timestamp limbs of `REL-MEM-008`.
- [Setty, Thaler, *Unlocking the lookup singularity with Lasso*](https://eprint.iacr.org/2023/1216)
  — the same fingerprinting machinery as used by the lookup argument; relevant if ROM
  membership is discharged by lookups rather than by the RAM class.
- [Yang, Heath, *Two Shuffles Make a RAM: Improved Constant Overhead Zero Knowledge RAM*](https://eprint.iacr.org/2023/1115)
  (USENIX Security 2024) — two vectors of access metadata, one in access order and one
  in address order, related by permutation proofs, with a *local* consistency check
  replacing the global one. Already cited by `GAP-MEM-007` for the address/value/version
  roles; it is the reference for the per-namespace ordering of `REL-MEM-012`, not for
  the aggregate identity.

- **\*\*\* GAP-MEM-009 — Pin the reference anchors.** Each reference above is
  verified by title, authors, venue, and year only. Record the exact section or
  construction number backing every normative claim that cites it, and align this
  module's notation with the cited one where they disagree.

## Metadata

- spec revision: draft
- implementation: baseline `zksync-airbender@303ea6fa+dirty`; encoding and
  product-binding subset checked at `31dcc31b8+dirty`
- profile: unrolled and unified execution

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| \*\*\* `REL-MEM-001` | normative | proof acceptance | `REL-MEM-006`; `REL-MEM-016` | prose | fingerprinted read/write multiset equality | — |
| \*\*\* `REL-MEM-002` | provisional | selected target | `GAP-MEM-008` | prose | stub; two challenge fields selected by recursion level and proof type | — |
| \*\*\* `REL-MEM-003` | normative | one product instance | `REL-MEM-002`; `REL-MEM-007..009`; `REL-MEM-013..015`; `GAP-MEM-008` | prose | one transcript-derived challenge shared by all partition products | — |
| \*\*\* `REL-MEM-004` | normative | every physical event row | `REL-MEM-003`; `REL-MEM-008`; `GAP-MEM-006` | located | common tuple fingerprint and selector-to-identity gate | `symbol:cs/src/definitions/constants.rs#NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES`; `symbol:gkr_eval_ir/src/lower/memory.rs#lower_memory_tuple`; `symbol:gkr_eval_ir/src/lower/memory.rs#mask_into_identity` |
| \*\*\* `REL-MEM-005` | normative | every declared partition | `REL-MEM-004`; `REL-MEM-013` | prose | product over encoded read-side and write-side multisets | — |
| \*\*\* `REL-MEM-006` | normative | one product instance | `REL-MEM-005`; `REL-MEM-013` | prose | labeled multiset union and associative product aggregation | — |
| \*\*\* `REL-MEM-007` | provisional | selected memory profile | `REL-MEM-008`; `GAP-MEM-004` | located | register/PC boundary insertion plus profile-specific memory initialization and teardown | `symbol:gkr_eval_ir/src/lower/memory.rs#lower_inits_or_teardowns`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| \*\*\* `REL-MEM-008` | provisional | every physical event row | `GAP-MEM-002`; `GAP-MEM-006` | located | recorded event schema reconciled with the current address-space term, six linearization challenges, and selector gate | `symbol:cs/src/definitions/gkr/mod.rs#AddressSpaceType`; `symbol:cs/src/definitions/constants.rs#NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES`; `symbol:gkr_eval_ir/src/lower/memory.rs#lower_memory_tuple` |
| `REL-MEM-009` | provisional | RAM-space data access | `REL-MEM-008`; `GAP-MEM-003` | located | adopted zero-valued RAM history for ROM loads; ordinary RAM transition remains incomplete | `decision:rom-zero-history-2026-09-16`; `symbol:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner`; `symbol:riscv_transpiler/src/replayer/mod.rs#ReplayerRam::mask_read_for_witness`; `symbol:riscv_transpiler/src/vm/ram_with_rom_region.rs#RamWithRomRegion::collect_inits_and_teardowns` |
| `REL-MEM-010` | provisional | proof acceptance | `external:EXEC`; `REL-MEM-007..008`; `GAP-MEM-001`; `GAP-MEM-002` | located | current PC-state grand-product construction and verifier boundary injection | `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation`; `symbol:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| \*\*\* `REL-MEM-011` | provisional | register or delegation event | `REL-MEM-008`; `GAP-MEM-003` | located | register namespace reused by delegation invocation and fulfillment; exact tuples unresolved | `symbol:cs/src/definitions/gkr/mod.rs#AddressSpaceType`; `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#accumulate_memory_like_grand_product` |
| \*\*\* `REL-MEM-012` | provisional | every address-space namespace | `REL-MEM-008..011`; `GAP-MEM-003` | located | current address-space separation; intended per-address ordering remains unresolved | `symbol:cs/src/definitions/gkr/mod.rs#AddressSpaceType`; `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#accumulate_memory_like_grand_product` |
| \*\*\* `REL-MEM-013` | provisional | selected profile | `REL-MEM-009..012`; `GAP-MEM-003` | located | event-class inventory and labeled output channels; owning modules remain incomplete | `symbol:cs/src/definitions/gkr/mod.rs#GKRMemoryLayout`; `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation` |
| \*\*\* `REL-MEM-014` | provisional | one product instance | `REL-MEM-008..013`; `GAP-MEM-004` | prose | stub; compiled instance shape and per-family setup comparisons not yet stated | — |
| \*\*\* `REL-MEM-015` | provisional | one product instance | `REL-MEM-008..014`; `GAP-MEM-008` | prose | stub; commitment inventory and absorption order not yet stated | — |
| \*\*\* `REL-MEM-016` | provisional | every partition-product pair | `REL-MEM-003..006`; `REL-MEM-013..015`; `GAP-MEM-005` | prose | stub; layered-circuit output-to-commitment binding not yet stated | — |
| `GAP-MEM-001` | open | — | affects `REL-MEM-010` and remaining common-memory scope; owner: human | — | common memory module remains partially integrated | — |
| \*\*\* `GAP-MEM-002` | open | — | affects `REL-MEM-008` and `REL-MEM-010`; owner: human | — | event schema recorded but not adopted, and its owning module not chosen | — |
| \*\*\* `GAP-MEM-003` | open | — | affects `REL-MEM-009` and `REL-MEM-011..013`; owner: human | — | ordinary RAM, register, delegation, ordering, and producer ownership remain incomplete | — |
| \*\*\* `GAP-MEM-004` | open | — | affects `REL-MEM-007` and `REL-MEM-014`; owner: human | — | profile boundaries, full-statement accumulation, and compiled-instance binding remain unspecified | — |
| \*\*\* `GAP-MEM-005` | open | — | affects `REL-MEM-016`; owner: human | — | no module states the layered-circuit claim binding each partition product to its committed rows | — |
| \*\*\* `GAP-MEM-006` | open | — | affects `REL-MEM-003..004` and `REL-MEM-008`; owner: human | — | challenge wire encoding recorded but not assigned to a serialization owner | — |
| \*\*\* `GAP-MEM-007` | open | — | affects `REL-MEM-009` and `REL-MEM-012..013`; owner: human | — | sorted-log framing and permutation lineage not decided for the memory instance | — |
| \*\*\* `GAP-MEM-008` | open | — | affects `REL-MEM-002..003` and `REL-MEM-015`; owner: human | — | commitment order, challenge position, and challenge-field selection unspecified | — |
| \*\*\* `GAP-MEM-009` | open | — | affects the References section; owner: human | — | cited papers verified by metadata only; section anchors not pinned | — |
