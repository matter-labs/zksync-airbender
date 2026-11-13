# Findings and dispositions

This register carries the result families and report dispositions from frozen #585,
commit `9501f1f45f075b61389bb301de697514bb61bed8`. The status refers to the single
ZKsync Airbender model. The [claim inventory](VERIFICATION_STATUS.md) gives each
statement, proof, witness and assurance boundary. No production circuit fix is claimed.

| Item | Status in this model | Claim or boundary |
| --- | --- | --- |
| F01: terminal PC | The typed full statement contribution derives terminal limb bounds. The noncanonical local case and its verifier-boundary rejection remain regressions. | [Verifier boundary](../lean/human/Human/Helpers/Context/VerifierBoundary/Theorems.lean) and [native machine targets](../lean/human/Human/Compiler/NativeTargets.lean). Cryptographic contribution binding remains external. |
| F02: bigint controls | Native undefined behavior includes invalid controls. Native targets do not assume valid delegation use. | The separate [bigint reference claim](../lean/human/Human/ISA/ValidUse/Theorems.lean) requires valid controls and RAM buffers. Controls 0 and 65537 are not claimed to be rejected. |
| F03: uncalled worker | Native clock constraints and initialized history supply occurrence accounting and caller scheduling. Historical zero-clock rejection remains a regression. | [Request and worker schedule claims](../lean/human/Human/Trace/Delegation/RVCallerTheorems.lean) and the complete native targets retain exact request matching. No external occurrence ledger is a target premise. |
| F04: worker ROM shadows | Native execution uses writable shadow RAM below the ROM boundary. It can differ from public ROM bytes. | [Valid reference use](../lean/human/Human/ISA/ValidUse/Model.lean) requires RAM buffers. Native targets do not claim ROM-pointer rejection. |
| F05: inactive rows | Boolean contribution masking projects the complete padded layout to active execution. Inactive rows need not stutter. | [Contribution boundary](../lean/human/Human/Helpers/Context/PaddingBoundary/Theorems.lean) and [padded targets](../lean/human/Human/Trace/Machine/Padding.lean). Native contribution authentication remains an interface. |
| F06: discarded loads | Loads into x0 follow the Airbender NOP behavior. This differs from unmodified Sail. | The [configured machine](../lean/human/Human/ISA/Sail/README.md) states the override. The run equivalence applies to that machine. |
| F07: control and participation | Worker constraints and participation remain explicit. Reference profiles retain their control and schedule conditions. | [Worker acceptance](../lean/human/Human/Trace/Machine/Model.lean) and [valid-use reference claims](../lean/human/Human/ISA/ValidUse/Theorems.lean). No general native validity check is claimed. |
| F08: hash protocol shape | Public decoded code and duration derive protocol counts and CSR families. Exact matching segments submitted workers. | [Code windows](../lean/human/Human/Trace/Machine/CodeWindows.lean), [segmentation](../lean/human/Human/Trace/Machine/Segmentation.lean) and separate valid-use reference profiles. |
| F09: table and decoder fidelity | All 16 setups have native imports and complete freshness checks. Fixed regions and the ROM fixture have trusted compiled comparisons. Native tuple preservation authenticates public decoder membership. | [Setup provenance](../lean/artifacts/setup/README.md) and [public setup binding](../lean/human/Human/Compiler/NativePublicSetup.lean). Arbitrary program/ROM binding and Rust/parser fidelity remain explicit. |
| F10: caller cycles versus execution | All three targets prove complete RV execution, including branches, jumps, loops, modular operations and matched delegation calls. Direct cached-native corollaries give machine runs. | [RV targets](../lean/human/Human/Trace/Machine/Theorems.lean) and [native machine-run targets](../lean/human/Human/ISA/Sail/NativeTargets.lean). Reference equality has its separate valid-use scope. |
| F11: hash witness contracts | Native execution models arbitrary admitted controls and Boolean round masks. Reference claims retain valid ABI profiles. | [Round-mask behavior](../lean/human/Human/Circuits/Blake2Round/Mask.lean) and [reference-use claims](../lean/human/Human/ISA/ValidUse/Theorems.lean). No production one-hot or control fix is claimed. |
| F12: split Keccak | The full unsigned target includes all three split workers. A complete 361-call valid schedule computes the reference permutation. | [Split worker claims](../lean/human/Human/Trace/Workers/KeccakSplit/RVTheorems.lean), [native targets](../lean/human/Human/Compiler/NativeTargets.lean) and the split reference-use claim. Worker constraints and exact matching remain interfaces. |
| F13: initialization and submitted pools | Targets accept lists of initialization instances under one checked top-bits list and include all submitted standard/split rows. The symbolic witness does not enumerate the windows. | [Initialization statements](../lean/human/Human/Circuits/InitsTeardowns/Theorems.lean) and [boot inputs](../lean/human/Human/Trace/Machine/Model.lean). The EVM verifier pins top bits (#548); the Rust verifier checks strict increase. Native unified windows reach only below 2^31. |

The following table records the 8 October dispositions in the frozen source.
It does not assert a later issue state.

| Report | Recorded disposition | Model scope |
| --- | --- | --- |
| [AIH-350](https://linear.app/matterlabs/issue/AIH-350) | Invalid sequences and interior entry are undefined behavior. Developers supply valid assembly sequences. | Native execution and valid reference use are separate claims. |
| [AIH-355](https://linear.app/matterlabs/issue/AIH-355) | Controls 0/65537: canceled without comment. | The model does not infer an individual technical reason or native rejection. |
| [AIH-357](https://linear.app/matterlabs/issue/AIH-357) | Extended-round controls: canceled. Upstream #491 fixes final-XOR selection but adds no one-hot rule. | Native Boolean masks and valid reference profiles have separate statements. |
| [AIH-358](https://linear.app/matterlabs/issue/AIH-358) | Invalid special5 control is undefined behavior. | Special5 has separate valid-use reference claims and is excluded from production targets. |
| [AIH-360](https://linear.app/matterlabs/issue/AIH-360) | G controls outside the schedule are undefined behavior. | Valid G profiles start at the documented counter. |
| [AIH-362](https://linear.app/matterlabs/issue/AIH-362) | Developers expect equal G state/message pointers to conflict with the full memory argument. | The valid reference profile requires separate buffers. The register does not infer a general circuit rejection. |
| [AIH-364](https://linear.app/matterlabs/issue/AIH-364) | Properly compiled programs avoid worker ROM pointers; other uses are undefined behavior. | Native shadow RAM remains distinct from public ROM; valid reference buffers lie in RAM. |
| [AIH-367](https://linear.app/matterlabs/issue/AIH-367) | Interior batch entry was described as divergence between prover CSR calls and simulation. | Native behavior and reference-profile behavior remain distinct scopes. |
