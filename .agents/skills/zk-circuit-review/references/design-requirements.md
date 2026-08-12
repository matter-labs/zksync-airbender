# Skill Design Requirements

Preserve these requirements when revising the skill:

- Keep the skill vendor-neutral and usable from a copied standalone skill folder.
- Require a user-supplied circuit name, path, or resolvable identifier. If none is supplied, ask which circuit to audit instead of selecting one or scanning the whole repository.
- Prefer one circuit. Permit an explicitly requested small group of tightly related circuits without silently expanding scope; keep resolution, coverage, evidence, and findings attributable to each target.
- Support AIR-like, PLONK-style, GKR, and hybrid row/layered algebraic circuits.
- Include enough self-contained context for a reviewer unfamiliar with the repository to begin a deep audit.
- Prefer high precision over report volume. Main findings must be reproducible soundness failures or material completeness failures.
- Put unresolved hypotheses, global dependencies, and non-security observations outside the main findings.
- Assume explicitly identified global/inter-circuit/inter-chunk mechanisms are sound, while fully auditing the named circuit's local interface to them.
- Use independent, skeptical validation when agent delegation is available and an equivalent sequential fallback otherwise.
- Never claim independent or cross-model validation unless it occurred.
- Keep orchestration bounded and preserve an honest coverage ledger.
- Keep repository-specific context optional, versioned, fingerprinted, and verified against the checked-out proving entrypoint. Never treat one project's profile as a vendor-wide or cross-system default.
- Keep the normative RV32I/M baseline vendor-neutral and separately provide exact official text references so reviewers do not reverse-engineer the ISA from code.
- Require each project profile to record a profile ID, repository/release/commit identity, validation date, applicability checks, active proving profiles, evidence map, known conflicts, and a maintenance rule for later versions.
- Route non-RISC-V targets away from every RISC-V and Airbender reference. A bundled reference is not automatically applicable.
- Distinguish normative semantics, project deviations, active profile/configuration, and observed enforcement. Treat simulators, witnesses, and tests as corroboration unless explicitly designated as specification.
- In each applicable versioned project profile, cover unsupported system/privileged operations, `rd=x0` preprocessing, alignment and ROM/RAM policy, optional M subsets, custom CSRRW/Zimop semantics, and verifier-defined I/O/termination. Do not place project-specific answers in the normative baseline.
- Cite exact primary papers for paper-derived lookup and memory mechanisms. Separate the stable semantic goal from version-specific implementations, adaptations, and omitted checks.
- For Airbender-like memory, document and separately audit register, RAM, preprocessed-ROM, PC/timestamp, delegation/precompile, and initialization/teardown behavior.
- Treat range-check-by-induction optimizations as explicit base/step/order/closure/separation proof obligations, not unexplained missing constraints.
- Avoid personal names, private conversation details, and organization-internal rationale not needed to execute the review.
- Add only independently verified historical examples. Keep blind evaluation answers outside the installed skill.
