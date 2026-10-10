## Arguments hierarchy

First see `Sharded and predicated execution` section. To conclude that abstract machine's execution was concluded correctly, the verifier need to check two kinds of arguments. Below we will call individual instances of various circuit types as "shards" or "chunks".

### Cross-chunk argument

To prove memory consistency argument one needs to ensure that read set and write set are permutations of each other. Such set equality argument is instantiated as grand product argument, and each circuit type outputs two scalars responsible to predicated in-chunk accumulation of encoding of read and write set elements respectively.

Predicated: for circuits where execution is predicated if predicate is `false` then corresponding contribution to grand product is multiplicative identity, otherwise (if predicate is `true`) - encoding of the element being added

Encoding: in a simple case of grand product based set equality (permutation) argument terms (encodings) like `element + random_challenge` are accumulated. For read/write sets' tuples we use batch encoding of all tuple's elements in a form of `(sum_i element_i * challenge_i) + additive_challenge_part`

To conclude the permutation argument prover provides to the verifier final entries for the read set for address space 2 (PC) and address space 1 (registers) for registers x0..=x31 in plain text, and provides the same for continuous subranges of the RAM address space as a part of inits/teardowns circuit type chunks (more on in below). Verifier performs encoding of such plain text final values itself and compares final accumutors for read and write set elements.

If set equality argument is valid AND local in-chunk timestamp comparisons are valid (details on the corresponding section below), then by the argument from the paper "two shuffles make a RAM" we can conclude that:
- for address space 0 (RAM) all reads and writes were consistent at addresses 0 mod 4 (restriction on there initial write set), and no accesses to other RAM addresses happened
- for address space 1 (registers) all reads and writes were consistent for registers x0..=x31 (due to non-trivial initial write set, and presence of final read set). For other register indexes elements in read and write sets form a permutation and NOT read/write memory
- for address space 2 (PC) where there is only single address value and corresponding initial write set entry, one can conclude that logically machine stepped over a series of cycles described by (PC, timestamp) where all timestamps are unique, and it's final (PC, timestamp) is the one provided in plain text to the verifier


Such cross-chunk argument now allows us to describe individual circuits in terms of the invariants and logical enforcements (we will not describe particular constraint here, just e.g. the fact that if particular opcode is executed, then entries added to read and write set are consistent with abstract CPU execuing this opcode over it's state. See interpretation of abstract machine in a corresponding file)

### Circuit type "family circuit"

TODO: add information about preprocessing and lookup argument. Decoder table as PC limbs (2xu16) as part of it's entries, with 2xField(-1) used for padding and unsupported opcodes

Invariants:
- if predicate = `true` then:
    - initial PC and final PC are 0 mod 4:
        - logically: follow RISC-V spec
        - implementation: prover provided initial PC value is added to read set and ASSUMED 0 mod 4 and ASSUMED properly split at u16x2, circuit enforced final PC value (determined by the executed opcode, and properly split at u16x2) is added to write set
            - proof: by induction and validity of permutation argument above, due to initial write set containing PC = 0 (= 0 mod 4)
    - initial timestamp is 0 mod 4, and final timestamp = initial timestamp + 4
        - logically: monotonic arrow of time
        - implementation: prover provided initial timestamp value is added to read set and ASSUMED 0 mod 4 and ASSUMED properly split at u19x2, circuit enforced final timestamp value (= initial timestamp + 4 without 2^38 overflow, properly split at u19x2) is added to write set
            - proof: by induction and validity of permutation argument above, due to initial write set containing timestamp = 4 properly split
    - register or RAM reads are logically consistent with a current machine's state
        - logically: machine doesn't change it state randomly and follows the arrow of time
        - implementation: prover provides read value witness (ASSUMED properly split as u16x2) and read value timestamp (ASSUMED properly split as u19x2). Then depending on the order of reads (TODO: details) the following entries are added to the read and write sets:
            - read set: address space, read value, read timestamp, address (derived from either decoder table (register indexes) or RAM offset computation (0 mod 4 additionally enforced by RAM offset computation case)). For registers with address >= 32 read timestamp is enforced to be 0
            - write set: same address space, write value (derived from rules of opcode being executed, is properly split as u16x2 by constraints), write timestamp being cycle's initial timestamp + 0/1/2, address (same as for read set).
        - proof: by induction: for registers x0..=x31 initial write set of consistent with rules, for RAM address space: inits and teardowns circuits only initialize 0 mod 4 RAM offset with 0 being the initial value. For registers with address >=32: initial write set is empty, and there is no final read set, and read timestamp is always 0 and can not be unique, so the only way to balance read/write sets is to have the matching entries being added by some other circuit - can be done in "precompiles" type, otherwise set equality will be violated


Enforced relations (we do not need to rely on set equality for them to be enforces - these are purely in-chunk local arguments):
- if predicate = `true` then:
    - initial PC belongs to the set of PCs supported by such circuit
        - logically: correcponding circuit family instance processes only supported opcodes
        - implementation: initial PC from above is a part of the lookup relation, predicated by the same predicate flag. If predicate is `true` but PC is not the one supproted (and in general also not 0 mod 4), then there is no such entry in decoder table, that would fail a lookup argument