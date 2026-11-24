module
public import Proven.NonVacuous.PooledBoot
public import Proven.NonVacuous.MachineBoot
public import Proven.InitsTeardowns.Native.Tokens
public import Proven.Compiler.NativeExtension.AddSub

@[expose] public section
namespace Airbender.NonVacuous.UnrolledNative
open Trace Trace.Machine Arithmetic Compiler NativeArithmetic
set_option warningAsError true

/-- One ADD row runs from zero registers with the complete standalone memory domain. -/
noncomputable def trace := PooledBoot.trace

/-- The production projection supplies the public ADD entry. -/
def entry : RVMachineProgramEntry :=
  (rvMachineProgramEntryWith .unrolledReduced PooledBoot.initial 0).get (by decide +kernel)

def program : List RVMachineProgramEntry := [entry]

/-- Both unrolled profiles decode this public instruction. -/
theorem program_image (config : RVMachineConfig)
    (profile : config = .unrolledFullUnsigned ∨ config = .unrolledReduced) :
    rvMachineProgramImage config PooledBoot.initial [0] = some program := by
  rcases profile with rfl | rfl <;> kernel_rfl

/-- Zero native teardown columns retain every RAM seed. -/
theorem teardown_tokens :
    PooledBoot.inits.flatMap InitsTeardowns.Witness.teardownTokens =
      PooledBoot.inits.flatMap InitsTeardowns.Witness.initTokens := by
  simp only [PooledBoot.inits, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact InitsTeardowns.Proofs.teardown_zero _ (fun _ _ => rfl)

/-- The native register terminals contain each architectural register once. -/
theorem register_addresses : (PooledBoot.registerTerminal.map MemoryToken.address).Perm
    (registerCells.map Cell.addressCode) := by
  decide +kernel

/-- The ADD instance meets all public boot and native teardown premises. -/
theorem boot (config : RVMachineConfig)
    (profile : config = .unrolledFullUnsigned ∨ config = .unrolledReduced) :
    BootInputs config trace PooledBoot.initial PooledBoot.cells program
      InitsTeardowns.importedLayout PooledBoot.inits := by
  refine ⟨PooledBoot.cells_facts.1, PooledBoot.cells_facts.2, rfl, ?_,
    ⟨[0], program_image config profile⟩, PooledBoot.topBits_checked, rfl,
    ⟨PooledBoot.registerTerminal, register_addresses, ?_⟩, rfl, PooledBoot.image, rfl, ?_⟩
  · intro index
    simp only [Cell.readRV, RV.State.getReg, PooledBoot.initial]
    split <;> rfl
  · change PooledBoot.registerTerminal ++ PooledBoot.inits.flatMap InitsTeardowns.Witness.initTokens = _
    rw [teardown_tokens]
  · exact ⟨⟨4, (8, 0)⟩, rfl, PooledBoot.accepted.states⟩

/-- The fixed public ADD program contains no special5 call. -/
theorem no_special : NoSpecial5 program := by
  intro candidate member
  obtain rfl := List.mem_singleton.mp member
  change some (RV.Instr.op .add 3 1 2) ≠ some (.delegate .keccak)
  intro impossible
  cases impossible

/-- The ADD row does not consume an external input. -/
theorem stream_ports : NonDeterminism.Pooled.StreamPorts trace PooledBoot.initial.input := by
  intro row member selected
  obtain rfl := List.mem_singleton.mp member
  have no_read : NonDeterminism.Pooled.isRead PooledBoot.row = false := by kernel_rfl
  rw [no_read] at selected
  cases selected

/-- The public setup uses the native fixed rows and the PC-indexed ADD entry. -/
noncomputable def tables := NativePublicSetup.rows PooledBoot.initial program

/-- The concrete native source assignment includes the ADD row's clock helpers. -/
theorem source_check : FullArithmeticNative.AddSubCached.native.artifact.source.all
    (fun polynomial => decide (evaluate (NativeExtension.AddSub.inputValues PooledBoot.assignment) polynomial = 0)) = true := by
  kernel_rfl

/-- Every source polynomial holds for the concrete ADD row. -/
theorem source_satisfied : Satisfies FullArithmeticNative.AddSubCached.native.artifact.source
    (NativeExtension.AddSub.inputValues PooledBoot.assignment) := by
  intro polynomial member
  exact of_decide_eq_true (List.all_eq_true.mp source_check polynomial member)

end Airbender.NonVacuous.UnrolledNative
