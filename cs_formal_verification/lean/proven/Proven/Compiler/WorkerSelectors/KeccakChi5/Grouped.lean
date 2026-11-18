module
public import Proven.Compiler.WorkerSelectors.Assemble
public import Proven.Compiler.WorkerSelectors.KeccakChi5.Part000
public import Proven.Compiler.WorkerSelectors.KeccakChi5.Part001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakChi5
set_option maxRecDepth 32768

/-- The contiguous batches cover every native query selector. -/
theorem batches : selectorsFor .chi5 = ([batch000, batch001]).flatten := by kernel_rfl

/-- Each worker selector belongs to its actual public native output chain. -/
theorem grouped :
    NativeLookups.groupsAgree (circuitFor .chi5) (selectorsFor .chi5) = true := by
  have accepted : AllBatches grouping [batch000, batch001] :=
    by
    refine ⟨?_, ?_, True.intro⟩
    · kernel_exact grouped000
    · kernel_exact grouped001
  rw [groups_agree_of_chains chain_groups]
  kernel_exact (congrArg (fun values : List NativeLookups.Selector => values.all grouping) batches).trans
    (flatten_all grouping [batch000, batch001] accepted)

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakChi5
