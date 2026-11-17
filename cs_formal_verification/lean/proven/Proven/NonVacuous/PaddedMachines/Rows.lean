module
public import Proven.NonVacuous.PooledBoot
public import Proven.NonVacuous.UnifiedBoot
public import Proven.WitnessCheck

@[expose] public section
namespace Airbender.NonVacuous.PaddedMachines
open Trace Arithmetic Verification
set_option warningAsError true

/-- The inactive ADD/SUB assignment retains its native PC, clock and comparison columns. -/
def pooledPaddingAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 2 ∨ column = 19 then 4
  else if column = 21 then 8
  else if column = 42 ∨ column = 43 ∨ column = 44 then 1
  else 0

/-- The inactive pooled row uses the actual imported ADD/SUB layout. -/
def pooledPadding : Row babyBearModulus PooledFamily := ⟨.addSub, pooledPaddingAssignment⟩

theorem pooled_lookup_tables :
    (FlatOperation.lookups (AddSub.importedConstraints (p := babyBearModulus))).map Lookup.table =
      (List.replicate 6 range16Checked).map CheckedTable.table := rfl

theorem pooled_timestamp_tables :
    (FlatOperation.lookups (AddSub.importedConstraintsTimestampLookups (p := babyBearModulus))).map Lookup.table =
      (List.replicate 8 timestampChecked).map CheckedTable.table := rfl

/-- The padding row satisfies every imported equation, range query and timestamp query. -/
theorem pooled_padding_satisfies : FlatOperation.ConstraintsHoldFlat (environment pooledPaddingAssignment)
    AddSub.clockConstraints :=
  holds_append (holds_of_checkOps pooled_lookup_tables (by kernel_rfl))
    (holds_of_checkOps pooled_timestamp_tables (by kernel_rfl))

/-- The imported execute column identifies this row as padding. -/
theorem pooled_padding_inactive : pooledPadding.assignment pooledPadding.columns.execute = 0 := rfl

/-- The inactive unified assignment retains its native PC, clock and comparison columns. -/
def unifiedPaddingAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 2 ∨ column = 30 then 4
  else if column = 32 then 8
  else if column = 123 ∨ column = 124 ∨ column = 125 then 1
  else 0

/-- The inactive unified row uses the actual imported machine layout. -/
def unifiedPadding : Row babyBearModulus UnifiedFamily := ⟨.machine, unifiedPaddingAssignment⟩

/-- The unified padding row satisfies its full imported description, including every lookup. -/
theorem unified_padding_satisfies : FlatOperation.ConstraintsHoldFlat (environment unifiedPaddingAssignment)
    (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.tableRV UnifiedBoot.initial)) :=
  holds_append (holds_of_checkOps UnifiedBoot.lookup_tables (by kernel_rfl))
    (holds_of_checkOps UnifiedBoot.timestamp_tables (by kernel_rfl))

/-- The imported unified execute column identifies this row as padding. -/
theorem unified_padding_inactive : unifiedPadding.assignment unifiedPadding.columns.execute = 0 := rfl

end Airbender.NonVacuous.PaddedMachines
