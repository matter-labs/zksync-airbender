module
public import Proven.Compiler.WorkerSelectors.Assemble
public import Proven.Compiler.WorkerSelectors.Bigint.Part000
public import Proven.Compiler.WorkerSelectors.Bigint.Part001
public import Proven.Compiler.WorkerSelectors.Bigint.Part002
public import Proven.Compiler.WorkerSelectors.Bigint.Part003
public import Proven.Compiler.WorkerSelectors.Bigint.Part004
public import Proven.Compiler.WorkerSelectors.Bigint.Part005
public import Proven.Compiler.WorkerSelectors.Bigint.Part006
public import Proven.Compiler.WorkerSelectors.Bigint.Part007
public import Proven.Compiler.WorkerSelectors.Bigint.Part008

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.Bigint
set_option maxRecDepth 32768

/-- The contiguous batches cover every native query selector. -/
theorem batches : selectorsFor .bigint = ([batch000, batch001, batch002, batch003, batch004, batch005, batch006, batch007, batch008]).flatten := by kernel_rfl

/-- Each worker selector belongs to its actual public native output chain. -/
theorem grouped :
    NativeLookups.groupsAgree (circuitFor .bigint) (selectorsFor .bigint) = true := by
  have accepted : AllBatches grouping [batch000, batch001, batch002, batch003, batch004, batch005, batch006, batch007, batch008] :=
    by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
    · kernel_exact grouped000
    · kernel_exact grouped001
    · kernel_exact grouped002
    · kernel_exact grouped003
    · kernel_exact grouped004
    · kernel_exact grouped005
    · kernel_exact grouped006
    · kernel_exact grouped007
    · kernel_exact grouped008
  rw [groups_agree_of_chains chain_groups]
  kernel_exact (congrArg (fun values : List NativeLookups.Selector => values.all grouping) batches).trans
    (flatten_all grouping [batch000, batch001, batch002, batch003, batch004, batch005, batch006, batch007, batch008] accepted)

end Airbender.Compiler.NativeWorkerLookups.Proofs.Bigint
