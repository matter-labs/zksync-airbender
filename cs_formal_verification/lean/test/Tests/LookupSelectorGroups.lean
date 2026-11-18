module
public import Human.Compiler.LookupSelectors
public import Proven.Compiler.ChainAddress
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeLookups
set_option maxRecDepth 32768

/-- Gate 5 belongs to the range table, so changing its group rejects the selector. -/
example : groupsAgree (circuitFor (.pooled .addSub)) [⟨0, 5, 0, []⟩] = false := by
  kernel_rfl

/-- The unchanged gate and operand still have their native range group. -/
example : groupsAgree (circuitFor (.pooled .addSub)) [⟨1, 5, 0, []⟩] = true := by
  kernel_rfl

/-- The table operand of gate 5 belongs to the 16-bit range chain and to no other chain. -/
example : groupsAgree (circuitFor (.pooled .addSub)) [⟨1, 5, 1, []⟩] = true := by
  kernel_rfl

example : groupsAgree (circuitFor (.pooled .addSub)) [⟨2, 5, 1, []⟩] = false := by
  kernel_rfl

/-- The single setup address that a resolved operand reads. -/
def readAddress : Except String Operand → Option GKRAddress
  | .ok ⟨_, .address address⟩ => some address
  | _ => none

/-- The table operand of gate 5 reads the 16-bit range column, not the timestamp column. -/
example : (readAddress (select (circuitFor (.pooled .addSub)) ⟨1, 5, 1, []⟩) ==
    readAddress (.ok (tableOperand (circuitFor (.pooled .addSub)) 1))) = true := by
  kernel_rfl

example : (readAddress (select (circuitFor (.pooled .addSub)) ⟨1, 5, 1, []⟩) ==
    readAddress (.ok (tableOperand (circuitFor (.pooled .addSub)) 2))) = false := by
  kernel_rfl

/-- The generic setup columns that a resolved operand reads. -/
def readColumns : Except String Operand → Option (List GKRAddress)
  | .ok ⟨_, .setup addresses⟩ => some addresses.toList
  | _ => none

/-- The generic table operand reads setup columns 0 to 7 only through its cache definition. -/
example : readColumns (select (circuitFor (.pooled .addSub)) ⟨0, 14, 1, [15]⟩) =
    some ((List.range 8).map .Setup) := by
  kernel_rfl

example : readColumns (select (circuitFor (.pooled .addSub)) ⟨0, 14, 1, []⟩) = none := by
  kernel_rfl

/-- The three public lookup outputs require one table operand each. -/
example : ([1, 2, 0] : List (Fin 3)).isPerm (outputGroups (circuitFor (.pooled .addSub))) = true := by
  kernel_rfl

example : ([1, 2] : List (Fin 3)).isPerm (outputGroups (circuitFor (.pooled .addSub))) = false := by
  kernel_rfl

end Airbender.Compiler.NativeLookups
