# Expanded Normative Sources

A verifier review needs the paper, not just the code — otherwise every bug
reads as a design decision. Use this list to find the construction the target
claims to implement, then audit against the paper's verifier.

**Before citing any identifier in a finding, confirm it resolves to the paper
named here.** These pointers are a starting map, not verified bibliography;
when the exact reference matters to a finding, fetch it and quote the relevant
section.

Prefer agent-navigable formats where they exist: IACR ePrint entry pages are
HTML with a PDF link; several of these papers also have arXiv HTML renderings;
Thaler's book and the bug trackers are HTML/Markdown.

## Foundations — read first if the protocol is unfamiliar

- **Thaler, *Proofs, Arguments, and Zero-Knowledge*.**
  `https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.html`
  The single best reference for sumcheck, GKR, multilinear extensions, and
  their verifiers. Chapters 4 (sumcheck) and 4.6 (GKR) give the exact verifier
  obligations this skill's `sumcheck-and-gkr-expanded.md` compresses. Use it to settle
  "what must the verifier check in round k".
- **Lund, Fortnow, Karloff, Nisan (1992)** — the original sumcheck protocol.
- **Goldwasser, Kalai, Rothblum (2008)** — the original GKR construction;
  **Cormode, Mitzenmacher, Thaler (2012)** for the practical refinement.

## Modern sumcheck-based systems

- **HyperPlonk** — ePrint 2022/1355. PLONK-style constraints over the boolean
  hypercube via sumcheck; the canonical reference for zerocheck-as-sumcheck,
  `eq`-gating, and batching several relations into one sumcheck. Directly
  relevant to layered designs that batch gates with powers of a challenge
  instead of add/mul selectors.
- **Spartan** — ePrint 2019/550. Sumcheck-based R1CS with a multilinear PCS;
  useful for the claim-reduction and PCS-handoff structure.

## Lookups and memory

- **Haböck, "Multivariate lookups based on logarithmic derivatives"** —
  ePrint 2022/1530. The LogUp identity, its soundness conditions, and the
  multiplicity requirements a verifier must enforce.
- **LogUp-GKR** — ePrint 2023/1284. LogUp evaluated through a GKR layer chain,
  which is the shape used when lookup lhs/rhs pairs are reduced by the same
  layer machinery as everything else.
- **Memory checking / offline memory checking** — ePrint 2023/1115 is the
  variant cited by this repository's own `docs/subarguments_used.md`; **Blum,
  Evans, Gemmell, Kannan, Naor (1991)** is the origin. The verifier-side
  obligations to extract: init/teardown structure, the `read_ts < write_ts`
  ordering requirement, and the permutation identity that closes the argument.

## STARK / FRI (previous-generation verifiers)

- **ethSTARK Documentation** — ePrint 2021/582. The most implementation-honest
  STARK write-up: constraint composition, DEEP, FRI parameters, and an explicit
  soundness/grinding analysis. Use its parameter discussion for the budget pass.
- **FRI** — Ben-Sasson, Bentov, Horesh, Riabzev (ICALP 2018);
  **DEEP-FRI** — ePrint 2019/336;
  **Proximity Gaps for Reed–Solomon Codes** — ePrint 2020/654 (the source of
  the batching/proximity soundness terms most implementations cite).

## WHIR and multilinear proximity

- **WHIR** — ePrint 2024/1586. The multilinear-code proximity argument used in
  place of FRI after a sumcheck/GKR reduction. Its verifier structure —
  out-of-domain samples, per-round sumcheck, folding, query openings — is the
  reference for `pcs-whir-expanded.md`. Its soundness section gives the per-round terms
  and the role of grinding in reducing query counts.

## Fiat–Shamir specifically

- **Attema, Fehr, Klooß, "Fiat–Shamir Transformation of Multi-Round
  Interactive Proofs"** — ePrint 2021/1377. What the transformation actually
  requires round by round; the formal basis for "every challenge must bind
  everything before it".
- **"Weak Fiat–Shamir Attacks on Modern Proof Systems"** — ePrint 2023/691.
  Concrete breaks of deployed systems from incomplete transcripts. The best
  single source for what the exploit actually looks like.
- **Trail of Bits, "The Frozen Heart vulnerability"** blog series. The
  canonical description of the drawn-before-committed pattern across
  Bulletproofs, PlonK, and Girault proofs.
- **OpenZeppelin, "Interactive sigma proofs and the Fiat–Shamir
  transformation"** audit write-up. Source of the round-table audit method
  used in `fiat-shamir.md`: reconstruct
  `round → prover data absorbed → challenge sampled → later dependencies` and
  verify every verification-relevant prover value is absorbed before the first
  challenge whose security argument requires it.

Recurring bug families these sources establish, restated for the round table:
missing transcript elements (public inputs, commitments, claimed outputs,
domain/circuit identifiers); wrong absorption order, where a prover-controlled
value is committed only after the challenge that should bind it; challenge
reuse across logically distinct rounds; missing domain separation between
protocols, rounds, and challenge types; prover/verifier transcript mismatch
from differing serialization, ordering, labels, or conditional branches;
partial binding, where only a digest or a subset of a structure is absorbed;
malleable or ambiguous serialization letting distinct objects share a transcript
encoding; challenge truncation/reduction mistakes when converting hash output
to field elements; challenges used before all required commitments are fixed;
reset/fork bugs from cloned or reinitialized transcript state; optional or
empty-message paths that skip the update; batching under challenges that do not
bind every batched item; missing statement/context binding permitting replay
across circuits, versions, chains, or public inputs; and multi-round dependency
mistakes where a later challenge fails to depend on everything that produced
the earlier one plus the subsequent prover message. In recursion, add: the
inner verifier key or inner public inputs not bound into the outer transcript.

## Solidity/Yul and the EVM execution boundary

Protocol papers do not specify calldata, Yul memory, compiler, deployment,
call, proxy, or settlement semantics. For an on-chain verifier use primary
execution sources:

- [Solidity inline assembly](https://docs.soliditylang.org/en/latest/assembly.html)
  for Yul and `memory-safe` compiler assumptions;
- [Solidity ABI specification](https://docs.soliditylang.org/en/latest/abi-spec.html)
  for canonical widths/offsets and packed-encoding ambiguity;
- [Solidity call/revert behavior](https://docs.soliditylang.org/en/latest/control-structures.html)
  for low-level call success semantics;
- [Solidity compiler options](https://docs.soliditylang.org/en/latest/using-the-compiler.html)
  and [known bugs](https://docs.soliditylang.org/en/latest/bugs.html) for the
  exact deployed code-generation pipeline;
- [Ethereum Yellow Paper](https://ethereum.github.io/yellowpaper/paper.pdf) for
  opcode-level arithmetic, calldata, memory, calls, and exceptional execution;
- activated EIPs on the target chain/fork, including
  [EIP-170](https://eips.ethereum.org/EIPS/eip-170),
  [EIP-211](https://eips.ethereum.org/EIPS/eip-211), and, for proxy deployments,
  [ERC-1967](https://eips.ethereum.org/EIPS/eip-1967).

Source Solidity is not the deployed verifier. Treat generated source, exact
compiler/settings, runtime bytecode, deployed address/configuration, helper
contracts, and settlement caller as one implementation chain. See
`evm-l1-verifier.md`.

## Bug corpora

- **0xPARC ZK Bug Tracker** — `https://github.com/0xPARC/zk-bug-tracker`.
  Markdown, agent-navigable. Mostly circuit bugs, but the "unchecked
  prover-supplied value" pattern transfers directly to verifier inputs.
- Public audit reports for comparable systems (Plonky2/3, Risc0, SP1, Miden,
  Boojum). Read the *verifier* sections; they are where the Fiat–Shamir and
  parameter findings live.

## Using these in a finding

Cite the paper section that states the obligation the verifier violates, and
quote it if it is short. "The paper requires X" without a section number is not
specification evidence. Where the target deliberately deviates from the paper,
cite the repository's own statement of the deviation and audit against *that*
claim.
