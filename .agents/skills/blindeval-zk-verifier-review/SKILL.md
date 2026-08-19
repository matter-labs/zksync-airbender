---
name: blindeval-zk-verifier-review
description: Blind-evaluate either zk-verifier-review-monolith or the zk-verifier-review coordinator-plus-specialists suite against one historical verifier or proof-argument bug. Use when given a domain-qualified example number, filename, slug, or title and asked whether a fresh Codex or Claude reviewer can independently rediscover the referenced bug in its recorded vulnerable commit without examples, later Git history, host memories, or the expected fix.
---

# Blind-Evaluate ZK Verifier Review

Use one historical case from `zk-verifier-review-monolith/examples/` as a hidden
answer key. Export its recorded vulnerable revision, remove project history and
all historical example corpora, inject either the monolith or the coordinator
suite, and launch one fresh isolated evaluator.

Use `scripts/blind_eval.py` for every fixture and run. Never substitute an
ordinary worktree or subagent: they can share Git objects, filesystem context,
memories, or examples with the source checkout.

Keep every run authorized, defensive, source-local, and read-only. The evaluator
may describe a bounded symbolic false-acceptance flow and remediation property,
but must not create proof-forging tools, runnable malicious provers, deployment
payloads, network probes, or live-system instructions.

## Select one reviewer and case

Require one reviewer:

- `monolith` injects only `$zk-verifier-review-monolith`;
- `coordinator` injects `$zk-verifier-review` and all six verifier specialists.

Accept one case selector from these domains:

```text
transcript
composition
gkr-whir
stark-fri
soundness
recursion-l1
```

Prefer `domain/selector`, for example:

```text
transcript/03
composition/exact-multiple-final-chunk
gkr-whir/01-maxquadratic-coefficients.md
recursion-l1/"Recursive proof output was not bound to the supplied program"
```

A globally unique filename, slug, or exact title also works. A bare number is
normally ambiguous because numbering restarts in every domain; do not guess.
The selector is outer-orchestrator input only. Never include the number, slug,
title, fix, vulnerable revision, or expected failure in the evaluator prompt.

Default the provider to the invoking client: Codex from Codex and Claude from
Claude. Accept explicit provider, model, effort, and timeout overrides.

## Prepare and verify

From the source repository run:

```bash
python3 .agents/skills/blindeval-zk-verifier-review/scripts/blind_eval.py prepare \
  --reviewer coordinator \
  --example 'gkr-whir/dimension-reduction-index-space'
```

Use `--reviewer monolith` for the historical all-in-one workflow. Optionally
pass `--case-id`, `--output-root`, `--corpus-skill`, or `--skills-root`.
Otherwise cases are written under
`.agents/output/blindeval-zk-verifier-review/`, which is ignored by Git.

Preparation must complete automatically. The script:

1. Resolves one case from the monolith's domain-grouped corpus.
2. Parses its fix, vulnerable revision, failure domain, and scoped historical
   paths from the reproduction command.
3. Exports the vulnerable revision with `git archive`, without source Git
   metadata or later objects.
4. Removes repository skills, plans, audits, outputs, Claude/Codex state, nested
   Git metadata, and every historical example corpus.
5. Injects only the selected reviewer skill set and records its tree digest.
6. Rejects residual occurrences of the hidden title or fix SHA.
7. Initializes a neutral one-commit repository with no remotes or alternates.
8. Stores `answer-key.md` and `manifest.json` outside the mounted evaluator
   fixture.

Read `case_dir` from the JSON and immediately verify it:

```bash
python3 .agents/skills/blindeval-zk-verifier-review/scripts/blind_eval.py verify \
  --case-dir <case-dir>
```

Stop on ambiguity, malformed metadata, unresolved revisions, residual examples,
unsafe symlinks, skill contamination, or isolation failure. Fix the corpus or
launcher; never weaken the check or hand-edit a fixture.

## Launch exactly one evaluator

```bash
python3 .agents/skills/blindeval-zk-verifier-review/scripts/blind_eval.py run \
  --case-dir <case-dir> \
  --provider codex
```

Use `--provider claude` when requested. Pass `--model`, `--effort`, or
`--timeout-seconds` only when needed.

Each fixture is single-use. Prepare a fresh case for every retry, provider,
model, effort, or reviewer. A monolith-versus-coordinator comparison therefore
uses two separately prepared fixtures with the same case selector and distinct
case IDs. Never reuse the first fixture for the second reviewer.

The launcher:

- mounts only the one-commit fixture, ephemeral runtime state, provider
  credentials, and optional read-only Rust caches;
- omits the source checkout, host home, user skills, memories, plugins, MCP
  servers, prior sessions, later commits, and every answer corpus;
- permits broad research for standards and unrelated reference implementations
  while prohibiting external lookup of the audited repository or its history;
- records JSON events, final output, provider/model metadata, injected reviewer,
  skill-tree digest, timeouts, and contamination findings;
- treats repository-specific external requests as contamination, including
  requests made by delegated provider agents.

Repository-specific path blocking is not uniform across hosted web tools. Treat
request-log inspection as an auditable control, not a perfect network boundary.
Model pretraining can also contain public knowledge that filesystem isolation
cannot remove.

## Grade against the referenced bug

After the run, read only from outside the fixture:

- `answer-key.md` for the hidden historical failure;
- the evaluator's `final.md` and, when necessary, `events.jsonl`;
- `run.json` for completion and contamination status.

Grade semantic rediscovery, not wording or commit archaeology:

- **catch** — the report identifies the same root prover freedom or incorrect
  verifier relation, locates the materially affected path/component, explains
  the false-acceptance or honest-proof failure, and treats it as a finding with
  enough source evidence to support remediation. Exact line numbers, names, or
  the historical fix are unnecessary.
- **partial** — the report reaches the same mechanism or broken invariant but
  leaves a material link unresolved, understates/misstates impact, finds only a
  strict subset, or retains the expected bug merely as an unverified lead.
- **miss** — the expected failure is absent, contradicted, closed incorrectly,
  or replaced only by generic advice or unrelated findings.
- **unscored** — provider failure, timeout, contamination, missing final report,
  malformed fixture, or another condition that prevents a fair recall score.

Do not upgrade a score because the evaluator found many unrelated bugs. Record
additional credible findings in grade notes, but score the selected referenced
bug alone. For a completeness case, require recognition of the honest-proof
failure rather than forcing a soundness narrative.

Record the grade:

```bash
python3 .agents/skills/blindeval-zk-verifier-review/scripts/blind_eval.py grade \
  --case-dir <case-dir> \
  --outcome <catch|partial|miss|unscored> \
  --notes '<brief evidence-based rationale>'
```

When comparing reviewers, grade them independently before reading the other
reviewer's report. Then compare selected-bug recall, evidence quality, false
positives, explicit coverage, elapsed time, and event volume. One case is not a
general benchmark; repeat across domains and seam bugs.

## Preserve and clean up

Keep the fixture through grading and miss analysis. Then run:

```bash
python3 .agents/skills/blindeval-zk-verifier-review/scripts/blind_eval.py cleanup \
  --case-dir <case-dir>
```

Cleanup removes only `fixture/`. It retains the hidden answer, manifest, raw
events, final report, run metadata, grade, stderr, and digested injected skills.
It refuses ungraded, failed, timed-out, contaminated, or incomplete runs unless
`--force` records an explicit decision to discard the fixture.

## Report the result

Report the reviewer, selected case, vulnerable commit, fixture verification,
provider/model/effort, exit and contamination status, grade and rationale, and
paths to `answer-key.md`, `final.md`, `events.jsonl`, `run.json`, and
`grade.json`. Do not call a provider failure or contaminated run a miss, and do
not claim independent comparison unless each reviewer received a fresh fixture.
