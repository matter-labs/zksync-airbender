module
public import Human.Circuits.Bigint.Memory
public import Slop.Bigint.Addresses
public import Slop.Bigint.NativeExecution
public import Slop.Bigint.WitnessCheck
public import Slop.KernelRfl

@[expose] public section

namespace Tests.BigintMemory
open Airbender Trace Arithmetic
set_option warningAsError true

def row (column : Nat) : ZMod babyBearModulus :=
  if column = 1 then 5
  else if column = 4 || column = 38 then 64
  else if column = 37 then 32
  else if column = 55 then 128
  else if column = 0 || column = 66 || column = 212 || column = 214 || column = 215 then 1
  else if 216 ≤ column ∧ column < 273 ∧ (column - 216) % 3 = 2 then 1
  else 0

def native : Delegation.Row babyBearModulus := ⟨.bigint, row⟩

theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Bigint.importedConstraints Bigint.setupTable) :=
  Bigint.holds_of_check (by kernel_rfl)

private theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Bigint.importedConstraintsTimestampLookups (p := babyBearModulus)) :=
  Bigint.timestamps_of_check (by kernel_rfl)

def setup : Delegation.Setup babyBearModulus :=
  ⟨Bigint.setupTable, { name := "unused", Contains _ _ := False },
    { name := "unused", Contains _ _ := False }, { name := "unused", Contains _ _ := False }⟩

def cells : List Cell :=
  [.register 10] ++ (List.range 8).map (fun i => .ram (BitVec.ofNat 32 (4194304 + 4 * i))) ++
    [.register 11] ++ (List.range 8).map (fun i => .ram (BitVec.ofNat 32 (4194336 + 4 * i))) ++
    [.register 12]

def data : Delegation.MemoryData babyBearModulus where
  setup := setup
  rows := [native]
  initial := native.memorySteps.map Prod.fst
  terminal := native.memorySteps.map Prod.snd

theorem accepted : Delegation.MemoryAccepted data := by
  constructor
  · intro current member
    simp only [data, List.mem_singleton] at member
    subst current
    exact Verification.holds_append core clocks
  · exact List.perm_append_comm

end Tests.BigintMemory
