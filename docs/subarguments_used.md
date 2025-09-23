# Small list of sub-arguments that we use

## Sharding and pre-commitments for permutation proofs

Standard arguments to prove permutation require drawing a common challenge, and as we drag along our memory argument across multiple circuits we have to pre-commit to such pieces of the trace before starting "full mode" proving of those individual pieces. Such pre-commitment is implemented via sending the columns that would be a part of permutation argument into separate subtree. Prover usually does the following:
- Generate a full memory witness, not even a full trace witness.
- Commit to them in a chunked form.
- Write them into the transcript and draw challenges.
- (actually forget all the work above except challenges).
- Start proving individual circuits using those external challenges for memory and delegation arguments. More on those below.
- In the recursive verification step - write down the same transcript using memory-related subtree commitments, and assert equality of the challenges from such regenerated transcript and those external challenges used during proving.

This way we do ~5-10% redundant work for pre-commit, but keep excellent degree of parallelism for individual proofs over circuit chunks.

## Memory argument

Memory argument is based on the permutation argument that uses read set and write set - there are various variants of papers, but here is one: ["Two Shuffles Make a RAM"](https://eprint.iacr.org/2023/1115.pdf). In a nutshell, every memory access updates read and write sets. We will show how such argument allows to avoid quite a few range checks, and also how to deal with the case of initialization/teardown to be provided at runtime.

Some refreshment on the memory argument linked above:
- It assumes init: A list of all, or at least those accessed, **unique(!)* addresses should form the initial write set. The original paper doesn't provide a good recipe for it, but it can be assumed to come from the setup, in a form of tuples that span all the address space, with 0 value and 0 timestamp at init.
- Every act of memory access comes as the below two actions. We do not touch here how the address of such access is computed, though.
    - Prover provides a "read timestamp" and "read value", and tuple of `(address, read_ts, read_value)` goes into the read set.
    - Time is somehow tracked/implemented to allow notion of ordering, and written value is also somehow computed. Then `(address, write_ts, write_value)` is added into write set
    - It's asserted that `read_ts < write_ts`.
- At the end, prover provides a teardown set for the same list of addresses as in the init, final value and last write timestamp are provided.
- At the end it's ensured that `init + write set` is a permutation of `teardown + read set`.

Now one step at the time we modify the argument: First we allow dynamic init. Note that argument requires **unique(!)** addresses in init/teardown by default. Instead we allow prover to provide a list of addresses, which we refer to as lazy init and teardown, with the following requirements:
- Each "cycle" prover can initialize an address.
- Addresses are `u32`, so comparison is well-defined.
- Init timestamp and value are hardcoded to 0.
- Either:
    - Next address is higher than current address.
    - Or current address, corresponding teardown timestamp and teardown value are 0.

This way, pre-padding with addresses equal to 0 allows to not tie number of addresses to number cycles, and contribution of such initializations in case of padding cancels each other in read/write sets.

Then, we keep in mind that `init + write set` is a permutation of `teardown + read set` and go over pieces of the `(address, value, timestamp)` tuple:
- Write timestamp are coming from setup, so whenever prover provides read timestamp, we do not need to range-check them - if permutation holds, then read timestamps are range-checked automatically.
- Then addresses - initialization checks that all addresses are range-checked, so whenever we use some variables as "address" - we have a free range check for them. Otherwise such address is not in initial write set or teardown read set, and with `read timestamp < write timestamp` being always enforced, it would break a permutation.
- Free range check on read value part is a little more convoluted, that's why it comes last. Assume that all parts explained above hold. That is enough to prove RAM consistency by the original paper in a sense that we can only read RAM from the "past". This way any prover-provided read value in range checked by induction:
    - Either it comes from the init - then it's 0.
    - Otherwise it is formed by RISC-V cycle circuit, that where IF read-value is range-checked, then written value is range checked. But any read-value here comes from the "past", so it's either 0 from init set, or range-checked by induction.

For efficiency, we model registers as a part of RAM argument with address space being formally a tuple of `(bool, u32)`, where boolean indicated whether it's a register or not, and `u32` is either register index, or memory address (`0 mod 4` in our circuits in practice). Timestamp is modeled as a pair of 19-bit integers, forming $2^{38}$ timestamps range, with 4 timestamps being used per row that allows us to run up to $2^{36}$ cycles without wrapping. Total number of cycles during single program invocation is checked by the verifier.

## Delegation argument

We allow our "kernel" OS to use separate circuits to prove some specialized computations. At the moment we only have a plan for U256 big integer ops, used for EVM emulation, and BLAKE2s/BLAKE3 round function, used both for: recursive verification, bytecode de-commitment, and storage implementation.

Technically, circuits that perform a delegation just read from and write into global RAM, but do so only if they have a corresponding request to process. A main circuit, one that proves RISC-V cycles, forms a set of requests in the form `(should_process_boolean, delegation type, mem_offset_high, write timestamp to use)`. Write timestamp is statically formed from the setup data and circuit index in the batch as usual, and `should_process_boolean`, `delegation type` and `mem_offset_high` are produced by RISC-V cycle. Such requests become part of the set equality argument in the form of `set_snapshot = \sum should_process/((delegation type, mem_offset_high, write timestamp to use) + randomness)` that resembles standard log-derivative lookup argument, but in case of boolean multiplicities it proves set equality.

Circuits that perform a delegation form the same set from their side, and `delegation type` is a constant defined for every particular circuit. To technically process a request such delegation circuits have their own ABI, for example, BLAKE2s round function circuit read/writes 8-word internal state of BLAKE2s hash, then reads 2 control words, and 16 words of the hashed data. Such RAM accesses are implemented using the same memory argument as described above, with three small differences:
- Write timestamp used is one coming from delegation set equality argument.
- 32-bit memory slot indexes are formed as `(mem_offset_high << 16) | (access_idx * size_of::<u32>())`, meaning that our ABI requires parameters to be continuous in RAM.
- If one doesn't process the request (`should_process_boolean == false`), we **require** that: `write timestamp to use`, all read timestamps, and all read values and write values are set to 0. This way such subset "cancels" itself in the RAM read/write sets and has no influence on RAM consistency.

There are two important things that allow us to have a number of RISC-V cycles larger that prime field's modulus but still be sound, even though classical log-derivative lookup argument can not be used in this case:
- On one site of the delegation set snapshot, when RISC-V circuits forms it, tuples of `(delegation type, mem_offset_high, write timestamp to use)` are unique as timestamps are unique. And forming of this set is constrained by the executed program's opcodes, so prover can not substitute arbitrary values into the corresponding columns at all.
- Verifier checks that total number of rows in all delegation circuits is less than field modulus. In those circuits, the prover provides a tuple of `(should_process_boolean, delegation type, mem_offset_high, write timestamp to use)` as a pure witness and could try to make exactly `|F|` same entries to trick the argument, which will be rejected by the verifier.

In the same manner as for memory arguments, delegation-related values live in the separate "memory subtree" to allow the pre-commit technique to be used. After that, all those delegation circuits are fully independent from the main RISC-V circuit and can:
1. Be proved separately and in parallel.
2) Have radically different sizes.
