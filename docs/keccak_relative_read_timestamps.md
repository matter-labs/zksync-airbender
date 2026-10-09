# Relative read timestamps in the Keccak theta/rho and chi5 circuits

ALL READ TIMESTAMPS ARE EXPLICITLY COMMITTED MEMORY COLUMNS. A SHARED READ TIMESTAMP IS NOT A
VIRTUAL ONE. EVERY PRIVATE INPUT OF A MEMORY PERMUTATION TUPLE IS A COMMITTED MEMORY-SUBTREE
COLUMN; ADDRESSES AND WRITE TIMESTAMPS ARE PUBLIC CONSTANTS OR FIXED AFFINE EXPRESSIONS IN
COMMITTED COLUMNS. FIAT-SHAMIR BINDS THE MEMORY COMMITMENTS BEFORE THE PERMUTATION CHALLENGES
ARE DERIVED.

In the theta/rho and chi5 circuits several memory accesses of one call *share* one committed
read-timestamp pair, and the distance between that pair and the call's invocation timestamp is
fixed by the control word. Both facts rely on canonical invocation sequences, which are the only
sequences the Keccak delegation is meant to support. This document describes which accesses
share a timestamp and why, what the sharing saves, and why it does not weaken the memory
argument or Fiat-Shamir.

## 1. What a delegation memory access commits

Each register or RAM access contributes a read tuple `(address space, address, read_timestamp,
read_value)` and a write tuple `(address space, address, write_timestamp, write_value)` to the
global memory permutation argument. On an active delegation row the write timestamp is the
committed invocation pair plus the fixed local offset 2, so it needs no separate per-access
columns: the invocation pair is committed once per row. A read-only access writes back the same
value with this new timestamp, so it also advances the address's last-touch timestamp: reads
count as touches.

In an honest execution the read timestamp is the timestamp of the previous touch of that
address, represented by two 19-bit limbs `(r_lo, r_hi)` that the prover commits as memory
columns. The permutation argument matches the read tuple against the write tuple that previous
touch produced.

No RAM tuple can reference a witness-subtree column or an arbitrary witness expression: its
private inputs are memory-subtree column indices, `RamReadQuery::read_timestamp` and
`RamWriteQuery::read_timestamp` being `[usize; 2]` into the committed memory layout
(`cs/src/definitions/gkr/ram_access.rs`), next to public constants such as register indices and
indirect-access offsets. It must stay that way.

An access with no fixed predecessor proves `read_timestamp < write_timestamp` limb by limb with
a boolean borrow and two 19-bit range checks. This per-access comparison is what column parity
and every other delegation circuit use for all of their accesses. Its cost is what makes the
64-bit state lanes expensive: one lane is two u32 words, so four read-timestamp memory columns,
two borrows and four timestamp-comparison lookups per lane.

## 2. The canonical invocation sequence

A Keccak-f1600 permutation is 361 delegation calls issued by the guest routine in consecutive
cycles: 24 rounds of five column parity calls, five theta/rho calls and five chi5 calls, then one
column parity call for the delayed final iota. Within a round the call positions are

| Call | Position in the round |
|---|---:|
| Column parity, column `x` | `x` |
| Theta/rho, column `x` | `5 + x` |
| Chi5, plane `y` | `10 + y` |

Every call reads x11 (the state pointer) and reads and writes x10 (the control word). The lanes
live in the 31-slot state at x11, slot `P_r[x + 5y]` during round `r`, and slots `25 + x` hold
the column parities `C[x]`.

One cycle advances the main timestamp by 4. A call with invocation timestamp `I` writes at
`I + 2`, so an address last touched `Δ` calls earlier carries the read timestamp

```text
read_timestamp = I + 2 − 4Δ.
```

In a canonical sequence `Δ` is known for every access of theta/rho and chi5, because the
schedule fixes which earlier call touched each slot last.

### Theta/rho, call `x`: 16 accesses, 4 shared timestamps

| Shared timestamp | Accesses | Last touched by | `Δ` |
|---|---|---|---:|
| registers | x10, x11 | the previous call, whichever circuit it was: every call touches both | 1 |
| state lanes | both words of `A[x, 0..4]`, 10 accesses | column parity `x`, which reads all five lanes of column `x` at once | 5 |
| `C[x − 1]` | both words, read only | `x = 0`: column parity 4; `x = 1`: column parity 0; `x ≥ 2`: theta/rho `x − 2`, which read it as its `C[x + 1]` | `[1, 6, 2, 2, 2][x]` |
| `C[x + 1]` | both words, read only | `x ≤ 2`: column parity `x + 1`; `x = 3`: theta/rho 0, which read `C[4]` as its `C[x − 1]`; `x = 4`: theta/rho 1, which read `C[0]` | `[4, 4, 4, 3, 3][x]` |

Indices wrap modulo 5. The two parity distances depend on `x`; they are selected by the one-hot
column flags that the theta/rho control lookup pins to the control word.

### Chi5, call `y`: 12 accesses, 6 shared timestamps

| Shared timestamp | Accesses | Last touched by | `Δ` |
|---|---|---|---:|
| registers | x10, x11 | the previous call | 1 |
| lane `j`, one per lane | both words of the lane that theta/rho column `j` wrote into plane `y` | theta/rho `j` | `5 + y − j` |

The circuit lists the plane's five lanes in theta/rho source-column order `j` rather than in
logical lane order: group `j` holds logical lane `i = (j + 2y) mod 5`, physical slot
`P_(r+1)[i + 5y]`. Its producer theta/rho `j` sits at position `5 + j` and chi5 `y` at `10 + y`,
hence `Δ = 5 + y − j`. The source-column order is a cyclic rotation of the plane, and chi commutes
with it, so the computed values and their destination slots are the same as with the logical
lane order. The `y` in the distance is an output column of the chi5 control lookup, not a free
witness: it equals the control word's iteration on active rows and zero on padding. Each lane
has its own pair because its distance differs.

### Column parity: per-access comparisons

Column parity uses the per-access comparison for each of its accesses. Its reads of the state in
round 0, and the first call of a batch, have no fixed predecessor, so there is no distance to
use.

## 3. What is shared and what is constrained

For each group the compiler allocates one read-timestamp pair in the memory subtree and one
boolean borrow `b` in the witness (`grouped_read_timestamp` in
`cs/src/gkr_compiler/delegation_mem_accesses.rs`). Every member access of the group puts that
same committed pair into its read tuple; its address, read value and write value are its own,
and both of its tuples are in the argument. A grouped access has the same tuples, in the same
format and with the same write timestamp, as an ungrouped one; the difference is that `N`
accesses of one row point at the same two committed columns instead of `N` distinct pairs.

In place of the per-access comparison, the group satisfies three constraints
(`compile_read_timestamp_group_constraints`), with `R = 2^19`, `e` the execute flag,
`(I_lo, I_hi)` the invocation timestamp and `k` the registered distance expression, which the
control lookups fix to `4Δ` on active rows and `0` on padding:

```text
r_lo = I_lo + 2e − k + R·b      (R1)
r_hi = I_hi − b                 (R2)
b (b − 1) = 0                   (R3)
```

These equations hold in the base field. They do not separately range-check the read limbs or
select their normalized representation: `(r_lo + R, r_hi − 1, 1 − b)` satisfies them whenever
`(r_lo, r_hi, b)` does. The memory argument matches both committed limbs to an actual producer's
pair, and for that normalized pair the witness sets `b = I_hi − r_hi`, which on active rows is 1
exactly when `I_lo + 2 < k`. The all-zero padding assignment satisfies R1 to R3.

## 4. Where the savings come from

An ungrouped access costs two memory columns, one borrow and two timestamp-comparison lookups. A
group costs two memory columns and one borrow, and no timestamp-comparison lookup.

| ungrouped → grouped | Theta/rho | Chi5 |
|---|---:|---:|
| Accesses | 16 | 12 |
| Shared timestamps (groups) | 4 | 6 |
| Memory columns for read timestamps | 32 → 8 | 24 → 12 |
| Witness borrows | 16 → 4 | 12 → 6 |
| Extra witness column (`y`) | 0 | 1 |
| Timestamp range-check lookups per row | 34 → 2 | 26 → 2 |
| Total committed columns | 240 → 204 | 213 → 196 |

The 24 memory columns that grouping saves in theta/rho are exactly: x10 and x11 sharing one pair
instead of two (2 columns), the ten state-lane words sharing one pair instead of ten (18
columns), and each parity's two words sharing one pair instead of two (2 + 2 columns). The two
timestamp lookups of a row are the range checks of the invocation timestamp limbs themselves.

## 5. Why sharing does not weaken Fiat-Shamir or the memory argument

Each tuple is formed from committed memory-subtree inputs and fixed public expressions. Sharing
a column only decides which input indices a tuple reads; no read timestamp is uncommitted. The
full-statement transcript absorbs the memory commitment caps before deriving the permutation
challenges, so every tuple input is bound before the challenges exist.

Soundness rests on two facts.

1. **R1 to R3 imply the per-access comparison.** Given any assignment satisfying R1 to R3, set
   the comparison borrow to `a = 1 − b`. The two range-checked expressions of the per-access
   comparison become `R − k` and `R − 1` on active rows and `R − 2` and `R − 1` on padding, all
   inside `[0, R)` because the control lookups give `0 < k < R` on active rows and `k = 0` on
   padding. So every witness that satisfies R1 to R3 also satisfies the read-before-write check,
   and sharing a pair only adds equalities between read columns. Nothing that the per-access
   comparison rejects is accepted.
2. **The permutation argument picks the real producer.** The global memory argument matches the
   exact address, value and timestamp limbs, with multiplicity. R1 to R3 therefore cannot
   replace an actual predecessor by a timestamp for which no matching write exists, or reuse a
   write that another read already consumes. Under the canonical invocation sequence the tables
   above identify each predecessor and its distance. A deviation that changes a grouped access's
   predecessor distance fails either the relative relation for the actual timestamp or the memory
   multiset for a forged one. These local relations do not independently enforce the entire
   361-call sequence or its entry point: all grouped predecessors lie within one round, so a gap
   between two rounds, or the first column parity call of a batch, is seen only by column
   parity's per-access comparisons. Those are obligations of the surrounding execution
   statement.

The relations are local to a row. They read no neighbouring row and carry nothing across
proofs, so a permutation may straddle two theta/rho or chi5 proofs; producers and consumers are
matched by the one global memory argument of the full statement: every main-machine and
delegation proof of a statement uses the same external challenges, and the full statement
verifier multiplies their read and write contributions before testing global equality
(`full_statement_verifier/src/unrolled_proof_statement.rs`). The invocation timestamp limbs are
range checked directly.

## 6. Implementation map

| Where | What |
|---|---|
| `cs/src/cs/circuit.rs`, `circuit_trait.rs`, `circuit_impl.rs` | `read_timestamp_group: Option<u8>` on register and indirect access requests; `set_read_timestamp_group_distance(group, expr)` |
| `cs/src/gkr_compiler/delegation_mem_accesses.rs` | one memory-subtree pair and one boolean per group, reused by every member; R1 and R2; registered and used group ids must match |
| `cs/src/gkr_compiler/layout.rs`, `cs/src/definitions/gkr/ram_access.rs` | `relative_timestamp_groups` (pair, borrow, member indices) and the per-access `Option<RamAuxComparisonSet>`; `None` means the access has no per-access comparison |
| `cs/src/gkr_circuits/delegation/keccak_f1600_gadgets.rs` | `grouped_control_register`, `grouped_state_lanes`, the registers group and its distance |
| `keccak_theta_rho/mod.rs`, `keccak_chi5/mod.rs` | the groups above and their distance expressions |
| `common_constants/src/delegation_types/keccak_f1600.rs` | the distance constants, the chi5 slot order, and a test that derives every distance from the 361-call schedule |
| `prover/src/gkr/witness_gen/delegation_circuits/memory.rs` | CPU witness: checks that all members recorded the same timestamp, then `b = I_hi − r_hi` |
| `gpu/trace/src/witness/memory_delegation.rs`, `native/witness/memory_delegation.cuh` | the same on GPU; fixed-size group ABI |
| `cs/src/gkr_compiler/aux_layout_test.rs` | every member's tuple references its group's committed pair, every read-timestamp column lies in the memory subtree, every memory-tuple cache relation depends on memory-subtree columns only, every ungrouped access has its comparison |
| `prover/src/tests/gkr/relative_timestamps.rs` | R1 to R3 on compiled layouts, limb-boundary borrows, the alternative limb representation, padding, and retimed, skipped and interleaved sequences |

A circuit that requests no groups gets the per-access comparison for every access.
