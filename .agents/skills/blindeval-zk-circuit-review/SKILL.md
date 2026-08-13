---
name: blindeval-zk-circuit-review
description: Blind-evaluate the zk-circuit-review skill against one of its historical bug examples. Use when given an example number, filename, slug, or title and asked to test whether a fresh Codex or Claude evaluator can independently rediscover that example's bug without seeing the example, later Git history, host memories, or the expected fix.
---

# Blind-Evaluate ZK Circuit Review

Take one `zk-circuit-review` example as the complete case specification. Derive
its vulnerable revision, fix, component target, and affected paths; remove all
examples that could reveal the same failure; then launch a fresh isolated
evaluator.

Every launched review is an authorized defensive correctness task. The
evaluator must use only source-local symbolic evidence and remediation guidance;
it must not produce runnable proof-generation exploits, operational attack or
reproduction procedures, deployment targeting, network probing, or access and
credential instructions. This boundary reduces unnecessary safety friction but
cannot guarantee that a provider-side automated check will never run.

Use `scripts/blind_eval.py` for every fixture and run. Never substitute a Git
worktree or ordinary subagent because they can share source Git objects or host
filesystem context.

## Accept the example selector

Accept exactly one selector in any of these forms:

- number: `13` or `#13`;
- filename: `11-memory-tuple-cache-unbound.md`;
- slug: `memory-tuple-cache-unbound`;
- exact example title.

Only top-level examples classified as scored historical circuit bugs are valid
targets. Records under `examples/hardening/` and `examples/implementation/` are
auxiliary collections, not benchmark cases. Refuse them; forcing an evaluator
to report hardening, witness-generation, or out-of-scope implementation behavior
would corrupt a circuit security-recall benchmark. The injected evaluator skill
must omit those auxiliary collections entirely.

Do not ask the user for a circuit, fix SHA, or vulnerable revision. The selected
example supplies them. Default the evaluator provider to the current client:
Codex when invoked from Codex and Claude when invoked from Claude. Accept an
explicit provider, model, or effort override when supplied.

Examples:

```text
$blindeval-zk-circuit-review 12
/blindeval-zk-circuit-review mem-subword-address-decomposition
$blindeval-zk-circuit-review "Subword memory address decomposition was not locally canonical or aligned" using Claude
```

The example selector is outer-orchestrator input only. Never include it, its
title, fix, expected bug, or excluded filenames in the evaluator prompt.

## Review semantic leakage

Before preparing the fixture, compare the selected example with every other
example's Classification, Intended relation, and affected reproduction paths.
Mark another example for exclusion when it is in the same circuit family and
could serve as a direct template for the selected finding because it exposes:

- the same constraint or algebraic relation with a different operand, column,
  branch, selector, sign, or output;
- the same lookup/table/witness binding failure in a closely analogous row or
  operation; or
- the same root error expressed at another layer, such as circuit construction
  and generated verifier enforcement.

Use a leakage-oriented test: if reading the other example would materially tell
the evaluator which local relation to inspect or how that relation is broken,
exclude it. Do not exclude an example merely because it names the same broad
circuit family, source file, opcode family, or proof system. When uncertain,
exclude the example and record the conservative choice.

This review is performed by the invoking agent outside the fixture. Do not put
its reasoning, classifications, titles, or selectors into the evaluator prompt.

## Prepare the fixture

Run from the source repository:

```bash
python3 .agents/skills/blindeval-zk-circuit-review/scripts/blind_eval.py prepare \
  --example '<number-or-name>' \
  --similarity-reviewed \
  --exclude-similar '<number-or-name>'
```

Repeat `--exclude-similar` for every semantic near-duplicate found. Omit only
that repeatable option when the completed review finds none. The mandatory
`--similarity-reviewed` acknowledgement prevents silently preparing a fixture
after considering only the selected file.

Optionally pass `--case-id` or `--output-root`. Otherwise the script creates a
timestamped case under
`.agents/output/blindeval-zk-circuit-review/`, which is ignored by Git.

Preparation must complete without manual interpretation. The script:

1. Resolves the selector uniquely against `zk-circuit-review/examples/`.
2. Parses `Fixed by`, `Vulnerable revision for reproduction`, `Component` or
   `Components`, and reproduction paths from the example.
3. Exports the recorded vulnerable revision with `git archive`, without source
   Git metadata.
4. Recursively removes historical project skills, audits, plans, Claude/Codex
   state, and nested Git metadata.
5. Copies the current `zk-circuit-review` skill, removing the selected example,
   every other example sharing any recorded equivalent fix commit, every
   semantic near-duplicate supplied by the leakage review, and their index rows.
6. Rejects any remaining occurrence of a recorded fix SHA or selected example
   title in the injected skill.
7. Creates `.claude/skills -> ../.agents/skills` for Claude discovery.
8. Initializes a neutral repository containing exactly one commit, no remotes,
   no alternates, and none of the source repository's later objects.
9. Writes the hidden case manifest outside the evaluator fixture.

Stop on an ambiguous selector, malformed example, unresolved revision,
escaping symlink, residual contamination, or failed isolation check. Do not
weaken a check or manually fill missing metadata; fix the example format or the
launcher instead.

## Verify and launch

Read `case_dir` from the preparation JSON, then run:

```bash
python3 .agents/skills/blindeval-zk-circuit-review/scripts/blind_eval.py verify \
  --case-dir <case-dir>

python3 .agents/skills/blindeval-zk-circuit-review/scripts/blind_eval.py run \
  --case-dir <case-dir> \
  --provider <codex-or-claude>
```

Pass `--model` or `--effort` only when requested. Do not pause between prepare,
verify, and run unless preparation or verification fails.

Every prepared fixture is single-use. Run exactly one evaluator attempt against
it. For a retry, provider-capacity failure, model change, repeated trial, or
second provider, rerun `prepare` with a new case ID and use the newly exported
fixture. Never reuse a case even when the prior attempt produced no final
message; the launcher rejects a second `run` command for the same case.

Keep the exported fixture through grading and any miss analysis. It preserves
the exact sanitized source that produced the trace. Record the hidden-answer
grade after any needed analysis, then reclaim the fixture's disk space:

```bash
python3 .agents/skills/blindeval-zk-circuit-review/scripts/blind_eval.py grade \
  --case-dir <case-dir> \
  --outcome <catch|partial|miss|unscored>

python3 .agents/skills/blindeval-zk-circuit-review/scripts/blind_eval.py cleanup \
  --case-dir <case-dir>
```

Cleanup removes only `fixture/`; it retains the manifest, raw event stream,
final report, run metadata, grade, stderr, and a digested snapshot of the
injected skill, so the skill version that produced the trace stays verifiable
after the fixture is gone. It refuses ungraded, failed, timed-out, contaminated,
or incomplete runs, whose fixtures are the ones most worth retaining;
`--force` overrides that after an explicit decision to discard the fixture.
Never clean a case you still intend to analyze.

The fresh evaluator receives only the example-derived component and affected
historical paths as its exact audit target. It does not receive the example
number, name, title, intended relation, bug class, fix, vulnerable revision, or
expected finding.

The launcher:

- exposes a minimal OS root, the fixture, ephemeral runtime state, credentials,
  and optional read-only Rust caches;
- omits the source checkout, host home, user skills, memories, plugins, MCP
  servers, and prior sessions;
- permits broad web research, including unrelated GitHub repositories, for
  standards, cryptographic background, audit techniques, and reference
  implementations;
- instructs the evaluator not to consult external copies, mirrors, newer
  versions, commits, diffs, issues, pull requests, or vulnerability reports for
  the particular repository being audited;
- derives repository-specific markers from the repository name, remote URL,
  target paths, selected-example title, and hidden source/fix commits;
- disables shell networking and browser/computer tools for Codex while leaving
  its logged hosted web search enabled;
- preserves JSON events and marks a request containing an audited-repository
  marker as a contaminated run, without scanning local command output.
- requests every reasoning-summary, raw-reasoning, partial-message, and
  subagent-text stream the provider CLI supports, while recognizing that a
  provider may still withhold private reasoning;
- scans nested tool-use events, so a delegated discovery role's web, MCP, or
  command requests are checked for audited-repository markers alongside the
  main agent's;
- records raw-event byte and event counts so the storage cost of partial-message
  capture is measurable per provider and model.

Repository-specific path blocking is not available uniformly across provider
web tools. Treat the request-log check as an auditable control rather than a
hard network boundary. Unrelated GitHub access is allowed and is not
contamination.

## Report the result

After the evaluator exits, report:

- selected example, fix-linked exclusions, and semantic-leakage exclusions;
- resolved vulnerable commit and one-commit/no-remote verification result;
- provider, model, effort, exit status, and contamination status;
- paths to `final.md`, `events.jsonl`, and `run.json`.

Grade the result only after completion, using the selected example outside the
fixture as the hidden answer key. Do not score a failed or contaminated run as
a miss. Preserve raw traces and repeat runs when comparing providers or models.

Filesystem isolation cannot erase knowledge acquired during model training. A
public page that describes the audited project without using any recorded
repository marker may also evade request-side detection. Record those residual
limitations when interpreting results.
