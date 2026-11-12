module
public import Human.Circuits.Bigint.Memory
public import Slop.Bigint.Addresses
public import Slop.Bigint.NativeExecution
public import Slop.Bigint.WitnessCheck
public import Slop.KernelRfl
public import Slop.NonVacuous.BigintPool

@[expose] public section

namespace Tests.BigintMemory
open Airbender Trace Arithmetic
set_option warningAsError true

-- The row, its constraint checks and its cells are the non-vacuity witness's (`Slop/NonVacuous/BigintPool.lean`).

def setup : Delegation.Setup babyBearModulus :=
  ⟨Bigint.setupTable, { name := "unused", Contains _ _ := False },
    { name := "unused", Contains _ _ := False }, { name := "unused", Contains _ _ := False }⟩

def data : Delegation.MemoryData babyBearModulus where
  setup := setup
  rows := [NonVacuous.Bigint.native]
  initial := NonVacuous.Bigint.native.memorySteps.map Prod.fst
  terminal := NonVacuous.Bigint.native.memorySteps.map Prod.snd

theorem accepted : Delegation.MemoryAccepted data := by
  constructor
  · intro current member
    simp only [data, List.mem_singleton] at member
    subst current
    exact Verification.holds_append NonVacuous.Bigint.core NonVacuous.Bigint.clocks
  · exact List.perm_append_comm

end Tests.BigintMemory
