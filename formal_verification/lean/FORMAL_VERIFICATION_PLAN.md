# Circuit formal verification plan

Backport the current formalization to Airbender v2 on dev while preserving its
small review surface, directory roles, pinned references and explicit trust
boundaries. This document is a snapshot of pending work; checked coverage lives
in [Verification status](VERIFICATION_STATUS.md), and accepted counterexamples
and unresolved connections live in [Findings](FINDINGS.md).

## Integrated review contract

Keep the same ownership boundaries as the source formalization:

- Review/Circuits owns selected references, artifacts, observable mappings and short public claims.
- Review/Helpers owns common properties, word representations, tables and local context.
- Review/Trace owns whole-execution and terminal-state contracts.
- Proofs owns calculations, selector recovery, native-equation checks and composition.
- Import owns the separate artifact-fidelity boundary.

Use original Clean constraint semantics and original pinned Sail standard clauses.
Reuse shared proofs unchanged when possible; record adaptations explicitly.
Derive local selectors, bounds and actual reads before promoting a row claim to
an initialized trace claim. Never hide a result or desired intermediate state in
an interface. Keep public assumptions visible and v2 findings independent.

## Continuing execution

The user authorized hourly continuation and regular commits on 17 October 2026.
The active schedule is Continue Airbender v2 formal verification backport, attached
to this backport chat. Keep working in the isolated dev-based worktree and commit
small verified milestones with Conventional Commits. Do not push without authorization.
Use the [serial bounded verification runner](scripts/check_all.py) and its
[validated watchdog](scripts/bounded_fv.py): one Lean worker, Lean memory cap
3072 MiB, total footprint at most 3072 MiB, resident at most 4096 MiB and finite
wall budgets. Confirm termination after limits and redesign instead of raising caps.
The original v3 schedule remains separate and paused.

## Pending integration work

Native direct shuffle-RAM/state metadata, ADD/SUB clock extraction and initialized
logical memory histories are checked. Accepted state/memory matching and initial
clock boundaries now derive all row/prior clock inputs, complete Clean memory
consistency and newest preceding reads. Public Sail image construction now binds
seed tokens and initial PC to actual reads, deriving initial bounds/clocks and
unique addresses. Ten-column native decoder placement/query order is checked,
including the separate zero flag. Selected-profile public Sail setup construction,
full padded logical membership, native padding exclusion and recovered zero flags
are checked. Initialized history now derives native read/write/terminal bounds;
canonical decoder PC/immediate and register-index bounds are checked. Native history
now constructs actual Sail reads/writes and intermediate states, including x0
preservation from v2 masked writes. Derived clock order groups complete rows;
readonly refreshes preserve the instruction pre-state even with aliases. Public
indexed PCs now derive every incoming PC alignment, including RV32 truncation.
Native equations derive bounded outgoing successors, and state matching bounds the
terminal PC. The proof layer now assembles all five arithmetic row interfaces
and original Sail preparation/execution/retirement from these derived facts and
actual native history. Rebased control transport derives PC reads and reaches the
actual masked write. Complete initialized five-opcode execution now composes
original Sail byte reads/decoding and normal steps to exact terminal PC/cells,
including empty traces. Native GPR metadata preserves all code bytes; actual pure
decoder evidence is retained from construction. A reversed two-row ADD/ADDI
witness derives PC 8 and x2=247 with no intermediate/result premise.

1. Finish binding native word-memory alongside checked arithmetic execution.
   All v2 equations/queries/metadata and native-shaped ROM tables now support
   checked transfer laws, alignment, exact ROM values and RAM-only stores.
   Native address arithmetic, modular PC successors and clock/port laws are also
   checked under explicit source/immediate/initial-PC and clock inputs.
   Public LW/SW decoding is now checked in a separate native registry: complete
   padded membership recovers actual original Sail source evidence, exact zero
   flags and PC/immediate bounds/alignment, including original x0 loads.
   Actual Sail byte extraction now binds native ROM data inside the public
   prefix; a complete four-MiB extraction covers every native ROM address.
   Initialized logical word-memory history now reuses shared matching, native
   clock recovery and decreasing-time range induction. Public seed construction
   derives all initial/per-row/prior clock inputs and all read/write/terminal
   word bounds, including discarded ROM-shadow reads; full decoder membership
   supplies the zero flag. Nonempty LW/SW/x0 fixtures and omitted-shadow rejection
   are checked. Initialized native-row assembly now derives effective-address
   addition, bounded aligned PCs, modular successors and clock/port order using
   existing native calculations unchanged, with no per-row numerical premises.
   Actual Sail cell realization and native row grouping are now checked with
   mixed-port x0 preservation, source-GPR transport and actual register/RAM writes.
   Reversed dependent store/load rows derive the intermediate RAM state and later
   read without a supplied state/read result. This realizes the full supplied
   native image, including shadow cells tracked as RAM. Native shadow accesses
   below four MiB now provably preserve their exact read value; native matching
   still retains every refresh token. Whole-address projection now preserves
   Clean consistency/latest writes and realizes only architectural cells in Sail.
   A separate public initializer reads architectural cells and retains canonical
   native shadow seeds independently; clocks, unique addresses, x0 preservation
   and complete row grouping are derived. The same constructor now supplies
   canonical seed bounds to the unchanged shared range induction, deriving all
   full native read/write/terminal ranges, including erased shadows. Ordinary/x0 ROM-load regressions retain
   full matching and actual masked Sail writes with unreadable shadow locations
   and distinct native shadow/ROM values. Projected initialization and public
   decoding now derive effective-address addition, bounded aligned PCs, modular
   successors and native clock/port effects through the existing calculations.
   Shared readonly-prefix transport recovers every retained port read in the
   instruction pre-state and the final actual masked write; native constraints
   prove that the final port always survives projection. Ordinary/x0 ROM loads
   and reversed dependent RAM store/load rows exercise these interfaces without
   supplied reads/intermediate states. Projected transfers now preserve every
   byte below four MiB, including missing bytes and code outside the tracked
   domain. Actual RAM writes remain outside that region. Successful public ROM
   extractions survive every projected prefix; public setup construction derives
   complete code-byte windows for programs fitting the native ROM region, and
   original Sail source/decoding evidence survives. A reversed dependent SW/LW
   regression simultaneously derives a real RAM change, retained ROM extraction
   and original code evidence without a later-read/result premise. Eight unchanged
   pinned Sail platform modules now discharge Machine translation, PMP/PMA and
   ordinary-memory helpers under public configuration. Actual projected native
   histories preserve that configuration. Native RAM reads/writes and alignment
   now feed original virtual-memory calls; the same reversed dependent SW/LW
   fixture derives a real virtual store and subsequent load without expected
   intermediate/read/state premises. Actual public ROM extraction and preserved
   prefixes now feed original Sail virtual ROM loads. Native address bounds derive
   their ordinary-address domain. Native masked writes now match the original LW
   destination effect, including x0 without NOP projection; the proof layer reaches
   the original ROM LW clause result in the actual native after-state. Ordinary/x0
   initialized fixtures construct actual ROM/decoder bytes and configuration while
   retaining shadow value 123 distinct from the loaded ROM word 0xc0001073.
   Original RAM LW/SW clauses now reach the actual native cell-transfer states.
   Native decoder fields derive opcode selectors, original registers and sign
   extension; retained native ports derive rs2 and RAM reads, including masked
   load writes/x0. The same reversed dependent fixture reaches original SW then
   LW clause results with actual read 123 and the actual destination write,
   without a supplied intermediate state/read or desired result. Original Sail
   nextPC preparation and PC retirement now compose all three RAM/ROM clause
   paths through unchanged control/history/configuration lemmas. Actual decoding
   selects original LW/SW; initialized effects derive the effective address and
   exact modular native PC successor. The small original Sail dispatcher is
   reused without v3's discarded-load profile. Ordinary/x0 ROM fixtures retire
   to native PC 4, and the same reversed SW/LW fixture reaches actual PC 8 and
   terminal RAM/x3 values 123 without intermediate/read/PC/result premises.
   [General initialized word-memory execution](Airbender/Review/Trace/Families/WordMemory/Theorems.lean)
   now composes every derived row through actual code reads, original decoding
   and normal preparation/clause/retirement. Public cell and shadow-seed domains
   discharge all local ordinary-RAM and actual ROM-prefix coverage conditions.
   Projected composition retains every native shadow token in matching and
   concludes the exact terminal PC and architectural cells, without equating
   shadow values with actual ROM bytes. The reversed dependent SW/LW fixture
   reaches PC 8 and RAM/x3=123 through this general relation; ordinary/x0 ROM
   loads and empty traces also pass. Configuration, public program size in ROM,
   ordinary public RAM and actual ROM extraction/seed coverage remain visible.
   [Fixed native zero boot](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean)
   now uses the unchanged original Sail initial profile and boot-image proof.
   Public domain geometry and native zero GPR/RAM/shadow seeds derive the general
   initialized execution boundary. Complete native paths keep terminal shadow
   values zero independently of actual ROM bytes. Ordinary/x0 boot fixtures reach
   native PC four and actual destination values; invented native seeds and
   nonzero public GPRs are rejected. The native proving-loader padding path was
   retested: it zero-extends the input words to four MiB, while the raw table
   constructor uses UNIMP only outside the image it receives. The separate
   [padding model](Airbender/Review/Helpers/Tables/WordROMPadding.lean) now proves
   full extent, unchanged prefix and zero tail symbolically. Next construct and
   verify actual Sail padding bytes and connect physical setup/initialization
   exports; the current model never fills absent Sail bytes implicitly.
   Rust refinement and cryptographic enforcement remain separate.
   Preserve v2 PC rollover and native timestamp offsets;
   keep physical setup generation/export and mixed/custom expansion explicit.
2. Add native jump/branch/SLT and extend the shared execution relation with checked
   control-flow interfaces. Preserve full native setup padding and actual public
   code-byte/decoder evidence; do not add per-row result or PC premises.
3. Port unsigned mul/div, shift/binop and subword memory into the same shared
   context; retain their family-specific assumptions and supported ISA profile.
4. Rebind bigint/BLAKE/Keccak workers and callers. Retest control validity,
   unissued workers, ROM behavior and request participation on v2 before reusing
   any source finding or temporary premise.
5. Port unified execution, protocol spans, terminal boundaries, padding and
   initialization/teardown under their actual v2 argument interfaces.

Expand importer support only when a concrete circuit requires it. The two native
word-memory fixed tables are now supported with exact three-column queries.
Other fixed tables, dynamic table selectors, 8-bit columns and state linkage
continue to fail closed.
Do not copy unused v3 Review theorems into the v2 build.

## Deferred milestones

Faithful Rust/JSON/Lean generation, full compiled argument correspondence,
cryptographic lookup/memory/statement enforcement and completeness remain
separate milestones. Every promoted public theorem needs a nonvacuous regression,
an explicit axiom root and resolved review-guide links.
