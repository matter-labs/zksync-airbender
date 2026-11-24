module
public import Proven.Compiler.WorkerSelectors.Assemble
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part000
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part001
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part002
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part003
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part004
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part005
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part006
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part007
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part008
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part009
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part010
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part011
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part012
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part013
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part014
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part015
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part016
public import Proven.Compiler.WorkerSelectors.BlakeRound.Part017

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
set_option maxRecDepth 32768

/-- The contiguous batches cover every native query selector. -/
theorem batches : selectorsFor .blakeRound = ([batch000, batch001, batch002, batch003, batch004, batch005, batch006, batch007, batch008, batch009, batch010, batch011, batch012, batch013, batch014, batch015, batch016, batch017]).flatten := by kernel_rfl

/-- Each worker selector belongs to its actual public native output chain. -/
theorem grouped :
    NativeLookups.groupsAgree (circuitFor .blakeRound) (selectorsFor .blakeRound) = true := by
  have accepted : AllBatches grouping [batch000, batch001, batch002, batch003, batch004, batch005, batch006, batch007, batch008, batch009, batch010, batch011, batch012, batch013, batch014, batch015, batch016, batch017] :=
    by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
    · kernel_exact grouped000
    · kernel_exact grouped001
    · kernel_exact grouped002
    · kernel_exact grouped003
    · kernel_exact grouped004
    · kernel_exact grouped005
    · kernel_exact grouped006
    · kernel_exact grouped007
    · kernel_exact grouped008
    · kernel_exact grouped009
    · kernel_exact grouped010
    · kernel_exact grouped011
    · kernel_exact grouped012
    · kernel_exact grouped013
    · kernel_exact grouped014
    · kernel_exact grouped015
    · kernel_exact grouped016
    · kernel_exact grouped017
  rw [groups_agree_of_chains chain_groups]
  kernel_exact (congrArg (fun values : List NativeLookups.Selector => values.all grouping) batches).trans
    (flatten_all grouping [batch000, batch001, batch002, batch003, batch004, batch005, batch006, batch007, batch008, batch009, batch010, batch011, batch012, batch013, batch014, batch015, batch016, batch017] accepted)

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
