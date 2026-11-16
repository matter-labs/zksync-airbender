module
public import Proven.Compiler.WorkerSelectors.Assemble
public import Proven.Compiler.WorkerSelectors.BlakeRound.Grouped
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

/-- Every worker query has its actual gate, expansion and native chain group. -/
theorem binding :
    NativeLookups.queryLocators (circuitFor .blakeRound) =
      .ok ((selectorsFor .blakeRound).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor .blakeRound).all (fun selector =>
      match NativeLookups.select (circuitFor .blakeRound) selector with
      | .ok _ => true | .error _ => false) = true ∧
    NativeLookups.groupsAgree (circuitFor .blakeRound) (selectorsFor .blakeRound) = true := by
  refine ⟨by kernel_rfl, ?_, ?_⟩
  · let predicate := fun selector =>
      match NativeLookups.select (circuitFor .blakeRound) selector with
      | .ok _ => true | .error _ => false
    have accepted : AllBatches predicate [batch000, batch001, batch002, batch003, batch004, batch005, batch006, batch007, batch008, batch009, batch010, batch011, batch012, batch013, batch014, batch015, batch016, batch017] :=
      by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
      · kernel_exact resolved000
      · kernel_exact resolved001
      · kernel_exact resolved002
      · kernel_exact resolved003
      · kernel_exact resolved004
      · kernel_exact resolved005
      · kernel_exact resolved006
      · kernel_exact resolved007
      · kernel_exact resolved008
      · kernel_exact resolved009
      · kernel_exact resolved010
      · kernel_exact resolved011
      · kernel_exact resolved012
      · kernel_exact resolved013
      · kernel_exact resolved014
      · kernel_exact resolved015
      · kernel_exact resolved016
      · kernel_exact resolved017
    kernel_exact (congrArg (fun values : List NativeLookups.Selector => values.all predicate) batches).trans
      (flatten_all predicate [batch000, batch001, batch002, batch003, batch004, batch005, batch006, batch007, batch008, batch009, batch010, batch011, batch012, batch013, batch014, batch015, batch016, batch017] accepted)
  · kernel_exact grouped

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
