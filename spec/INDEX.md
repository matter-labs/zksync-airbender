# Airbender Proof-System Specification

- spec-revision: `2026-08-28.5`
- implementation: `matter-labs/zksync-airbender@dfb1b2a8a+dirty`
- profile: `airbender-v3-gkr-2026-08-11`
- profile-applicability: `changed`
- profile-delta: `MACH and BASE require reconciliation after upstream sync; ADD was checked at the implementation revision above`

## How to read statement IDs

| Prefix | Meaning | Test |
|---|---|---|
| `REQ` | requirement enforced by this component | What equation or predicate must hold? |
| `INV` | invariant preserved across a transition or proof layer | If it holds before, must it hold after? |
| `REJ` | explicitly forbidden case | Which condition must make acceptance impossible? |
| `GAP` | unresolved specification question | What must a human decide or further evidence establish? |

`ASM` imports a guarantee from another component. `OUT` exports a guarantee to
another component. `IN` defines an admitted input domain.

[Specification metadata](METADATA.md) defines authority, activation, dependency,
source, anchor, binding, and gap fields. Claims remain in the readable module body;
metadata is consolidated at the bottom.

## External deliverable guide

[Ethproofs W2 coverage](ETHPROOFS-W2.md) maps the EF Cryptography Team's W2
whitepaper requirements onto this specification. W2 is a documentation target, not
an additional proof-system relation.

## Modules

| ID | Path | Scope | Status |
|---|---|---|---|
| `MACH` | [machine/execution.md](machine/execution.md) | machine profiles; initial state; cycle state | draft |
| `ADD` | [machine/add-sub.md](machine/add-sub.md) | integer add/subtract family subrelation | prototype |
| `BASE` | [statement/base.md](statement/base.md) | base-proof acceptance; program binding; output | draft |
| `DEC` | `machine/decoder.md` | authenticated decode; operand routing; selectors | planned |
| `REG` | `machine/registers.md` | register reads, writes, and `x0` | planned |
| `MEM` | `machine/memory.md` | RAM/ROM addressing, alignment, loads, stores | planned |
| `ISA` | `machine/instructions/` | per-instruction state transitions | planned |
| `DELEG` | `machine/delegation.md` | invocation/fulfillment relation and ABI | planned |
| `GARG` | `arguments/global.md` | memory, state, and delegation products | planned |
| `GEN` | `conformance/generation.md` | compiled-layout and generated-verifier agreement | planned |
| `GKR` | `gkr/statement.md` | layered circuit and Sumcheck relation | planned |
| `TRANS` | `transcript.md` | Fiat-Shamir transcript and challenge binding | planned |
| `WHIR` | `whir/statement.md` | PCS/WHIR commitment and opening relation | planned |
| `RECUR` | `recursion/statement.md` | recursive verification and chain relation | planned |
| `PUB` | `statement/final.md` | end-to-end verifier inputs, acceptance, output | planned |

## Dependency DAG

`A -> B` means module `A` assumes outputs of module `B`.

```text
MACH  -> DEC, REG, MEM, ISA, DELEG
ADD   -> DEC, REG
BASE  -> MACH, GARG, GKR, TRANS
GKR   -> TRANS, WHIR
GARG  -> TRANS
RECUR -> BASE, MACH, GARG, GKR, TRANS
PUB   -> BASE, RECUR

GEN   (artifact-conformance module; no semantic imports yet)
```

## Global gaps

- **GAP-SYS-001 — Production proof targets.** Which interfaces are normative:
  base, recursion-unrolled, recursion-unified, or all three?
- **GAP-SYS-002 — Production security profile.** Which field, extension, security
  level, PoW, cap size, FRI/WHIR schedule, and Blake-round mode are normative?
- **GAP-SYS-003 — Terminal proof artifact.** Does the specification end at the
  current proof artifact or include a future SNARK wrapper?

## Global-gap metadata

| ID | Status | Affects | Evidence | Owner |
|---|---|---|---|---|
| `GAP-SYS-001` | open | `MACH`, `BASE`, `RECUR`, `PUB` | `docs/end_to_end.md#Generate a proof artifact`; `tools/cli/src/prover_utils.rs#ProofTarget@0aa0d393bc98fa46a2b0365d2636a98a0409b606` | human |
| `GAP-SYS-002` | open | `GKR`, `TRANS`, `WHIR`, `RECUR`, `PUB` | `circuit_defs/setups/src/program_setups.rs#commit_setup_params@0aa0d393bc98fa46a2b0365d2636a98a0409b606`; implementation configuration only | human |
| `GAP-SYS-003` | open | `PUB` | `docs/end_to_end.md#SNARK wrapping status` | human |
