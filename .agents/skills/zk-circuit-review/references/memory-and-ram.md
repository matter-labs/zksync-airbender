# Memory, RAM, and Permutation Review

## Exact construction reference

The paper baseline is Yibin Yang and David Heath, [*Two Shuffles Make a RAM: Improved Constant Overhead Zero Knowledge RAM*](https://eprint.iacr.org/2023/1115), Cryptology ePrint Archive, Paper 2023/1115 (2023), published at the [33rd USENIX Security Symposium](https://www.usenix.org/conference/usenixsecurity24/presentation/yang-yibin) (2024).

The repository may change its grand products, shuffles, tuple compression, initialization scheme, timestamp representation, chunking, or verifier completion. The stable security goal does not change: the argument must emulate the intended RAM or permutation relation. For RAM, each read at a logical location must observe the value established by its latest preceding write under the intended timestamp order, with initialization and finalization closing the history. For a pure bus/permutation use, every produced tuple must be matched by the intended consumer with no unauthorized source or sink.

Treat the paper as a conceptual and cryptographic reference, not as evidence that the implementation copied every paper detail. Enumerate and audit repository-specific changes explicitly.

## Generic per-circuit obligations

When the global RAM/permutation mechanism is outside the named-circuit scope, assume only that it correctly checks equality or ordering of the tuples it receives. Audit whether this circuit produces the correct tuples:

- address-space or operation type;
- full logical address and limb encoding;
- read and write timestamps, local offsets, and strict-order conditions;
- read and write values;
- selectors and execution/padding behavior;
- initialization/finalization participation;
- tuple compression challenges and output wiring;
- distinction between stateful RAM semantics and a stateless permutation bus.

For every read or write, trace the tuple fields back to constrained local semantics. A globally consistent wrong tuple remains a local soundness bug.

## Airbender uses of the argument

The current Airbender architecture reuses one memory-like tuple format for several logically different relations. The semantic tuple is

```text
(type, address, timestamp, value)
```

with `type = Register (0)`, `RAM (1)`, or `PC (2)` and integer fields split into range-checkable limbs. Confirm the exact widths and compression order in the branch; the architecture currently describes `address: u32`, `timestamp: u38`, and `value: u32`.

### Register access

Ordinary RISC-V registers use `type = Register` and addresses `0..31`. Reads carry the prior value; read-write accesses also emit the constrained next value at the cycle's write timestamp. The initial register set is zero, and final register values may be verifier-bound public state.

Audit register-index derivation, special `x0` behavior, read/write timestamps, limb encodings, write-value constraints, and initialization/finalization. Check profile- or opcode-specific accesses rather than assuming all families use identical slots.

### RAM access

Mutable memory uses `type = RAM`, a 32-bit byte address, timestamped reads/writes, and 32-bit values. Word and subword circuits may choose an aligned word address while separately constraining byte selection, sign extension, and write masks. Audit alignment, address calculation and overflow, ROM-region selection, read-before-write ordering, local timestamp offsets, partial-write reconstruction, and the connection between the arithmetic result and emitted write value.

### ROM access through a preprocessed lookup

The low ROM region is represented inside the RAM address space but is not authenticated by ordinary mutable-RAM contents. The current architecture initializes those RAM locations to zero and emits concrete, semantically ignored memory traffic to keep the global argument well formed. The actual instruction or ROM value is enforced through an authenticated preprocessed bytecode/ROM lookup; stores to the ROM region are intended to be unsatisfiable.

Audit both halves independently:

- the memory-like tuple has the intended address, timestamp, neutral/placeholder value behavior, and activation;
- the lookup binds the requested ROM address and returned bytes/instruction to the committed preprocessing/setup data and the local operation.

Do not claim that the RAM argument authenticates the ROM value. Check that a prover cannot select RAM behavior for ROM, ROM behavior for RAM, omit the lookup, or combine a valid lookup at one address with memory traffic at another.

### PC and timestamp state

Machine state uses `type = PC`, normally with an empty address field. A non-delegation execution cycle consumes `(start PC, start timestamp)` and produces `(next PC, start timestamp + cycle stride)`, where current architecture uses a stride of four. The next PC is instruction-dependent. Initialization and finalization bind initial/final PC and total execution time to the verifier-visible statement.

Audit next-PC semantics, timestamp increment and overflow/range rules, type/address constants, execute/padding masking, and the exposed start/end state. Do not assume the permutation proves that `next PC` is correct; it only links the locally constrained state transitions.

### Delegation and precompile bus

Delegation reuses `type = Register` with virtual addresses beyond the base-register range, but it is intentionally a permutation bus rather than initialized RAM. Invocation circuits currently emit zero-valued tuples at the delegation/CSR identifier with a zero read timestamp and a write timestamp derived from the cycle state plus a local offset. The corresponding delegation/precompile circuit emits the mirrored tuple orientation so the global permutation closes. These virtual locations deliberately have no ordinary register initialization or teardown.

Audit the delegation identifier, type tag, zero values, exact timestamp orientation and offset, invocation selector, fulfillment selector, and mirroring across the two circuit families. Verify that ordinary register accesses cannot alias the virtual bus and that an invocation cannot close against the wrong precompile or an inactive/padding row.

### Initialization and teardown

Unrolled proving may use a dedicated inits/teardowns circuit, while a unified circuit may build the same contribution inline. These sets establish the base and closure for register, RAM, and PC histories and can inject public final state. Delegation locations are intentionally excluded.

During a per-circuit audit, list initialization/teardown correctness as a global assumption if it is external, but still verify whether the named circuit uses an initialized address space and exports the tuple format expected by that mechanism.

## Modified or omitted direct checks

Current code intentionally omits some checks that a standalone tuple implementation might perform:

- Some register/RAM read values are not directly range checked. The stated induction is that initialized values are in range and every write value is range checked, so a globally consistent later read must also be in range.
- Some witness-supplied memory address limbs in word/subword circuits are not directly range checked. The stated induction relies on range-valid initialization and teardown addresses, enforced timestamp inequalities, and the absence of unmatched intermediate read/write pairs outside those histories.
- PC and timestamp limbs may inherit validity from a valid initial state plus range-checked transitions rather than receiving a fresh check on every read tuple.
- Delegation intentionally omits initialization/teardown and uses zero-valued mirrored tuples because it is a permutation bus, not stateful RAM.

Do not report an omitted direct range check merely because it is absent. First prove or refute the full induction:

1. **Base:** every initialized/public starting value and address satisfies the claimed range and representation.
2. **Step:** every possible write or state update, under every selector, produces a range-valid value/address/timestamp.
3. **Order:** timestamps and local offsets force reads to match an earlier allowed write rather than an uninitialized or cyclic source.
4. **Closure:** teardown/finalization prevents unmatched out-of-range pairs and binds the intended terminal state.
5. **Separation:** address-space tags, ROM selection, and delegation virtual addresses cannot cross-match unintended histories.

If all five hold under the assumed global argument, the omitted local check is justified. If any circuit path violates a premise, construct the resulting globally consistent malformed history; that may be a confirmed local underconstraint or a clearly labeled global-interface dependency.
