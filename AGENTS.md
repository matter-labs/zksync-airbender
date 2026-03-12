# AGENTS.md

## Repo Rules
- Keep changes task-focused; avoid unrelated refactors.
- Avoid dependency or version churn unless explicitly requested.
- If a subdirectory has its own `AGENTS.md`, follow it for that area.

## Commits And PRs
- Use Conventional Commits for commit messages and PR titles, for example `fix(gpu_prover): shorten lock scope`.
- Keep the scope meaningful and specific to the area changed.
- Use `.github/pull_request_template.md` when preparing PR descriptions.
- Make sure the PR title matches the actual change, since PR titles feed changelog generation.

## GPU Work
- Only if the task touches GPU-related code or runs local GPU work, read `.agents/gpu_work.md`.
