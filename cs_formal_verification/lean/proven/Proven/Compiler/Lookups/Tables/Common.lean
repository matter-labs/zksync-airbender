module
public import Human.Compiler.NativeLookups
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeLookups.Proofs.Tables

/-- Kernel-evaluated checks of one table selector list give the table-side statement. -/
theorem tableSidesRead_of (circuit : Circuit) (tables : List Selector)
    (located : tableLocators circuit = .ok (tables.map fun selector => (selector.gate, selector.operand)))
    (grouped : (tables.map Selector.group).isPerm (outputGroups circuit) = true)
    (read : tables.map (select circuit) = tables.map fun selector => .ok (tableOperand circuit selector.group))
    (chained : groupsAgree circuit tables = true) : TableSidesRead circuit :=
  ⟨tables, located, List.isPerm_iff.mp grouped, List.map_inj_left.mp read, chained⟩

end Airbender.Compiler.NativeLookups.Proofs.Tables
