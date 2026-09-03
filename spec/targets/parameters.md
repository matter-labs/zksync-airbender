# Target parameters

## BabyBear Sec100

All BabyBear targets use its degree-four extension, seven-round Blake2s, cap size 16,
two base-oracle values per leaf, and a `2^4`-coefficient plaintext tail. Standard base
LDE factor is 2.

| Trace | Folds | Queries | Intermediate LDE factors | WHIR PoW bits |
|---:|---|---|---|---|
| `2^20` | `[1,5,5,4,4]` | `[87,11,7,6,5]` | `[256,8192,32768,524288]` | `[28,27,25,25,21]` |
| `2^22` | `[1,5,5,5,5]` | `[87,15,8,6,5]` | `[64,2048,32768,524288]` | `[28,25,27,25,21]` |
| `2^23` | `[1,5,5,5,4]` | `[87,23,10,7,5]` | `[16,512,16384,524288]` | `[28,24,25,19,21]` |
| `2^24` | `[1,5,5,5,4,3]` | `[87,23,10,7,5,5]` | `[16,512,16384,524288,524288]` | `[28,24,25,19,21,21]` |

The L1 feeder is a `2^23` unified recursion verifier using the special-opcodes machine.
It raises the base LDE factor to 16 and uses folds `[1,5,5,5,4]`, queries
`[21,17,9,5,4]`, intermediate LDE factors `[32,1024,32768,1048576]`, and WHIR PoW
bits `[29,26,25,26,21]`.

## Proth120 L1

The L1 wrapper uses Proth120 directly, Keccak256, one `2^22` delegation-free unified
trace packed by `2^4` into a `2^26` WHIR message, base LDE factor 32, cap size 8, four
base-oracle values per leaf, and a `2^4`-coefficient plaintext tail. Its folds are
`[2,4,4,4,4,4]`, queries `[17,12,8,6,5,4]`, intermediate LDE factors
`[128,2048,32768,524288,8388608]`, WHIR PoW bits `[30,30,27,25,21,24]`, and external
challenge PoW is 20 bits.

## Derived PoW

Lookup-challenge and initial WHIR batching PoW are derived per compiled circuit from
the lookup-identity degree and total committed-column count. A generated verifier pins
the resulting values; a target must not substitute a generic constant.
