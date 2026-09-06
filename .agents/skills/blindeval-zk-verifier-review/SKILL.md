---
name: blindeval-zk-verifier-review
description: Blind-evaluate exactly one zk-verifier-review coordinator specialist against one matching historical verifier bug example. Use when given a verifier-review domain or sub-skill plus an example number, filename, slug, or title—such as "transcript audit example 1"—and asked to launch a fresh Codex or Claude reviewer that must rediscover the verifier defect without examples, later Git history, host memories, the coordinator, other specialists, or the expected fix.
---

# Blind-Evaluate One ZK Verifier Specialist

Take a domain and one example from that domain. Build a sterile snapshot at the
example's recorded vulnerable revision, inject only the corresponding
specialist, and launch one fresh isolated evaluator.

Use `scripts/blind_eval.py` for preparation, verification, launch, grading, and
cleanup. Never substitute an ordinary worktree or an in-process subagent: they
can share Git objects, filesystem context, memories, or answer examples with the
source checkout.

Keep every run authorized, defensive, source-local, and read-only. The evaluator
may describe a minimal bounded correctness counterexample and remediation
property, but must not create executable demonstrations, deployment payloads,
network probes, credential/access steps, or live-system instructions.

Frame both manager and evaluator work as a benign historical correctness
regression. Limit deliverables to root cause, verifier acceptance or rejection
consequence, remediation, and defensive regression tests. Do not request or
produce operational exploitation guidance.

## Resolve the domain and example

Require both values. Map natural names to these canonical domains and skills:

| Domain | Also recognize | Injected specialist |
|---|---|---|
| `transcript` | Fiat-Shamir, proof input, parsing | `zk-verifier-transcript-review` |
| `composition` | cross-circuit, global arguments, chunks | `zk-verifier-composition-review` |
| `gkr-whir` | GKR, Sumcheck, MLE, WHIR | `zk-gkr-whir-verifier-review` |
| `stark-fri` | AIR, STARK, DEEP-ALI, FRI | `zk-stark-fri-verifier-review` |
| `soundness` | security bits, PoW, grinding, field | `zk-verifier-soundness-review` |
| `recursion-l1` | recursion, verifier binary, EVM, Solidity, L1 | `zk-recursion-l1-verifier-review` |

Thus `transcript audit example 1` means `--domain transcript --example 1`.
Accept an example number, filename, slug, or exact title from that specialist's
verifier-evaluable corpus: main examples plus `latent/`. Numbering is local to
the selected domain, so a bare number is valid after the domain is known. Cards
under `producer-parity/` or `implementation/` are historical reference material,
not blind-evaluation targets. A domain may temporarily have no evaluable
historical example; report that honestly instead of promoting a producer bug.
Every evaluable card must name a concrete `Verifier anchor`; treat its absence
as malformed corpus metadata rather than inferring one from the fix. Use that
neutral verifier anchor as the evaluator's bounded starting surface. It may name
a verifier artifact, entrypoint, generated-code family, or acceptance boundary,
but must not disclose the hidden failure, fix, reduction location, expected
relation, or reproduction paths. Immediate verifier callers/callees and the
corresponding emitted/generator artifacts remain in scope when needed to decide
the anchor's acceptance predicate; the entire repository does not.
Do not guess a missing domain and do not test an example under a different
specialist.

The domain and selector are outer-orchestrator inputs only. Never include the
example number, filename, slug, title, fix, vulnerable revision, failure text,
impact/fix text, reduction location, or reproduction paths in the evaluator
prompt.

Default the provider to the invoking client: Codex from Codex and Claude from
Claude. Accept explicit provider, model, effort, and timeout overrides.

## Prepare, verify, and launch

From the source repository, prepare the selected specialist case:

```bash
python3 .agents/skills/blindeval-zk-verifier-review/scripts/blind_eval.py prepare \
  --domain transcript \
  --example 1
```

Optionally pass `--case-id`, `--output-root`, or `--skills-root`. Otherwise write
the case under `.agents/output/blindeval-zk-verifier-review/`, which is ignored
by Git.

Preparation must complete automatically. The script:

1. Resolves the example only inside the selected specialist's corpus.
2. Parses its fix, vulnerable revision, failure domain, explicit verifier
   anchor, and historical reproduction paths. Only the neutral verifier anchor
   scopes the evaluator; the rest remains hidden answer and grading metadata.
3. Exports the vulnerable revision with `git archive`, without source Git
   metadata or later objects.
4. Removes repository skills, plans, audits, outputs, Claude/Codex state, nested
   Git metadata, and every historical example corpus.
5. Injects exactly one specialist with its `examples/` removed. It also copies
   the shared reference directories required by that specialist without copying
   the coordinator, another specialist, or another `SKILL.md`.
6. Rejects residual occurrences of the hidden title or fix SHA.
7. Initializes a neutral one-commit repository with no remotes or alternates.
8. Stores `answer-key.md` and `manifest.json` outside the mounted evaluator
   fixture.

Read `case_dir` from the preparation JSON and immediately verify it:

```bash
python3 .agents/skills/blindeval-zk-verifier-review/scripts/blind_eval.py verify \
  --case-dir <case-dir>
```

Stop on ambiguity, malformed metadata, unresolved revisions, residual examples,
unsafe symlinks, any second discoverable skill, answer contamination, or
isolation failure. Fix the corpus or launcher; never weaken the check or
hand-edit a fixture.

Then launch the evaluator rather than stopping after fixture preparation:

```bash
python3 .agents/skills/blindeval-zk-verifier-review/scripts/blind_eval.py run \
  --case-dir <case-dir> \
  --provider codex
```

Use `--provider claude` when appropriate. Pass `--model`, `--effort`, or
`--timeout-seconds` only when requested or needed. Each fixture is single-use;
prepare a fresh case for every retry, provider, model, or effort.

The launcher mounts only the one-commit fixture, ephemeral runtime state,
provider credentials, and optional read-only Rust caches. It omits the source
checkout, host home, user skills, memories, plugins, MCP servers, prior sessions,
later commits, the coordinator, other specialists, the monolith, and every
answer corpus. Shared reference-only directories are available solely because
the specialist's relative links require them.

Broad research is allowed for standards and unrelated reference
implementations. External lookup of the audited repository or its history is
contamination. Request-log inspection is an auditable control rather than a
perfect hosted-web boundary, and model pretraining may contain public knowledge
that filesystem isolation cannot remove.

The evaluator prompt must make verifier implementation the primary target. It
must tell the reviewer to use theory to derive obligations, spend most of the
run checking the concrete acceptance predicate, use the prover only as a format
or specification cross-reference, and proceed with the supplied verifier anchor
without requesting narrower scope. It must also require completion of the
anchor's verifier obligations after any candidate finding; unrelated leads do
not end the run.

## Grade the selected bug

After the run, read only from outside the fixture:

- `answer-key.md` for the hidden historical failure;
- the evaluator's `final.md` and, when necessary, `events.jsonl`;
- `run.json` for completion and contamination status.

Grade semantic rediscovery, not wording or commit archaeology:

- **catch** — identifies the same incorrect verifier acceptance or rejection
  relation and resulting prover freedom, locates the materially affected
  path/component, explains the false-acceptance or honest-proof failure, and
  supports remediation with source evidence;
- **partial** — reaches the mechanism or broken invariant but leaves a material
  link unresolved, misstates impact, finds only a strict subset, or keeps it only
  as an unverified lead;
- **miss** — omits, contradicts, or incorrectly closes the expected failure, or
  supplies only generic advice or unrelated findings;
- **unscored** — provider failure, timeout, contamination, missing report,
  malformed fixture, or another condition preventing fair recall scoring.

Do not upgrade the score for unrelated findings. For a completeness case,
require a verifier defect that rejects a canonical proof. Producer failure that
merely causes a correct verifier to reject is not an evaluable completeness
vulnerability.

Record the grade:

```bash
python3 .agents/skills/blindeval-zk-verifier-review/scripts/blind_eval.py grade \
  --case-dir <case-dir> \
  --outcome <catch|partial|miss|unscored> \
  --notes '<brief evidence-based rationale>'
```

This skill measures one specialist on one in-domain example. Do not use it for
coordinator routing, monolith comparison, cross-domain seam bugs, or multi-bug
campaign scoring.

## Preserve, clean up, and report

Keep the fixture through grading and miss analysis. Then run:

```bash
python3 .agents/skills/blindeval-zk-verifier-review/scripts/blind_eval.py cleanup \
  --case-dir <case-dir>
```

Cleanup removes only `fixture/`. It retains the hidden answer, manifest, raw
events, final report, run metadata, grade, stderr, and digested injected skill
tree. It refuses ungraded, failed, timed-out, contaminated, or incomplete runs
unless `--force` records an explicit decision to discard the fixture.

Report the domain, specialist, selected case, vulnerable commit, fixture
verification, provider/model/effort, exit and contamination status, grade and
rationale, and paths to `answer-key.md`, `final.md`, `events.jsonl`, `run.json`,
and `grade.json`. Do not call a provider failure or contaminated run a miss.
