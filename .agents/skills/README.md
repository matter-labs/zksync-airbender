# security-skills


Defensive, read-only ZK circuit and verifier review skills.

## Setup

- Skills: [`.agents/skills`](.)
- Claude link: [`.claude/skills`](../../.claude/skills) -> `../.agents/skills`

## Pick a skill

> **Codex users:** replace `/skill-name` with `$skill-name`, or run `/skills` to select a skill. Examples below use Claude syntax.

| Skill | Use for |
| --- | --- |
| `/zk-circuit-review` | Find missing or incorrect constraints in one ZK circuit |
| `/zk-verifier-review` | Plan and coordinate a full verifier audit |
| `/zk-verifier-transcript-review` | Check proof parsing and whether challenges bind data in the correct order |
| `/zk-verifier-composition-review` | Check invariants that span circuits, proofs, or chunks |
| `/zk-gkr-whir-verifier-review` | Check Sumcheck, GKR, and WHIR math and claim handoffs |
| `/zk-stark-fri-verifier-review` | Check legacy STARK and FRI proof verification |
| `/zk-verifier-soundness-review` | Verify claimed security bits from the actual parameters |
| `/zk-recursion-l1-verifier-review` | Check recursive proofs and on-chain verification boundaries |
| `/zk-verifier-review-monolith` | Audit an entire verifier in one historical all-in-one run |
| `/blindeval-zk-circuit-review` | Test whether the circuit skill rediscovers a historical bug |
| `/blindeval-zk-verifier-review` | Test whether a verifier specialist rediscovers a historical bug |

- Whole system: use `/zk-verifier-review`.
- Specific system domain: use the matching specialist.
- One circuit / circuit family: use `/zk-circuit-review`.
- More circuits: use prompting

## Skill calling examples

Replace `REPO` with the prover/verifier repository path. Replace `CIRCUIT` with
a circuit name or path.

```text
/zk-circuit-review Review CIRCUIT.
/zk-verifier-review Review the prover/verifier in REPO.
/zk-verifier-transcript-review Review the prover/verifier in REPO.
/zk-verifier-composition-review Review the prover/verifier in REPO.
/zk-gkr-whir-verifier-review Review the prover/verifier in REPO.
/zk-stark-fri-verifier-review Review the prover/verifier in REPO.
/zk-verifier-soundness-review Review the prover/verifier in REPO.
/zk-recursion-l1-verifier-review Review the prover/verifier in REPO.
/zk-verifier-review-monolith Review the entire prover/verifier in REPO.

/blindeval-zk-circuit-review 12
/blindeval-zk-verifier-review transcript 1
```

Blind verifier domains: `transcript`, `composition`, `gkr-whir`, `stark-fri`,
`soundness`, `recursion-l1`.
