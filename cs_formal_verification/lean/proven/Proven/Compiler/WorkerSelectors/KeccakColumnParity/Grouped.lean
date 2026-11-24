module
public import Proven.Compiler.WorkerSelectors.Assemble
public import Proven.Compiler.WorkerSelectors.KeccakColumnParity.Part000
public import Proven.Compiler.WorkerSelectors.KeccakColumnParity.Part001
public import Proven.Compiler.WorkerSelectors.KeccakColumnParity.Part002
public import Proven.Compiler.WorkerSelectors.KeccakColumnParity.Part003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakColumnParity
set_option maxRecDepth 32768

/-- The contiguous batches cover every native query selector. -/
theorem batches : selectorsFor .columnParity = ([batch000, batch001, batch002, batch003]).flatten := by kernel_rfl

/-- Each worker selector belongs to its actual public native output chain. -/
theorem grouped :
    NativeLookups.groupsAgree (circuitFor .columnParity) (selectorsFor .columnParity) = true := by
  have accepted : AllBatches grouping [batch000, batch001, batch002, batch003] :=
    by
    refine ⟨?_, ?_, ?_, ?_, True.intro⟩
    · kernel_exact grouped000
    · kernel_exact grouped001
    · kernel_exact grouped002
    · kernel_exact grouped003
  rw [groups_agree_of_chains chain_groups]
  kernel_exact (congrArg (fun values : List NativeLookups.Selector => values.all grouping) batches).trans
    (flatten_all grouping [batch000, batch001, batch002, batch003] accepted)

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakColumnParity
