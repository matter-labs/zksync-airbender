module
import all Mathlib.Data.List.Sort
public import Std.Data.TreeSet.Lemmas
public import Proven.GKRProtocol.Functional
public import Proven.GKRProtocol.CleanPlacementChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.NumericFunctionalStepChecks

structure Data where
  known : List Nat
  outputs : List (Nat × Nat)
  inputs : List (Nat × Nat)

def port (isBase : GKRAddress → Bool) (address : GKRAddress) : Nat × Nat :=
  (AddressUniqueChecks.addressCode address, if isBase address then 1 else 0)

def encode (isBase : GKRAddress → Bool) (entry : List GKRAddress × FunctionalStep) : Data where
  known := entry.1.map AddressUniqueChecks.addressCode
  outputs := entry.2.outputs.map (port isBase)
  inputs := entry.2.inputs.map (port isBase)

def stepCheck (data : Data) : Bool :=
  distinct (data.outputs.map Prod.fst) &&
    data.outputs.all (fun output => output.2 == 0 && !data.known.contains output.1) &&
    data.inputs.all (fun input => input.2 == 1 || data.known.contains input.1)

def check (data : List Data) : Bool := data.all stepCheck

theorem contains_code (items : List GKRAddress) (address : GKRAddress) :
    (items.map AddressUniqueChecks.addressCode).contains (AddressUniqueChecks.addressCode address) =
      items.contains address := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem]
  constructor
  · intro member
    obtain ⟨original, included, same⟩ := List.mem_map.mp member
    exact CleanPlacementChecks.addressCode_injective same ▸ included
  · intro member
    exact List.mem_map.mpr ⟨address, member, rfl⟩

theorem distinct_code (items : List GKRAddress) :
    distinct (items.map AddressUniqueChecks.addressCode) = distinct items := by
  apply Bool.eq_iff_iff.mpr
  simp only [distinct_iff]
  exact ⟨List.Nodup.of_map AddressUniqueChecks.addressCode,
    fun unique => unique.map CleanPlacementChecks.addressCode_injective⟩

theorem flag_zero (value : Bool) : ((if value then 1 else 0 : Nat) == 0) = !value := by
  cases value <;> rfl

theorem flag_one (value : Bool) : ((if value then 1 else 0 : Nat) == 1) = value := by
  cases value <;> rfl

theorem stepCheck_encode (isBase : GKRAddress → Bool) (known : List GKRAddress)
    (step : FunctionalStep) : stepCheck (encode isBase (known, step)) = step.check isBase known := by
  simp only [stepCheck, encode, FunctionalStep.check, List.map_map, List.all_map, port,
    Function.comp_def, flag_zero, flag_one, distinct_code, contains_code]

theorem check_sound (isBase : GKRAddress → Bool) (entries : List (List GKRAddress × FunctionalStep))
    (data : List Data) (binding : data = entries.map (encode isBase)) (checked : check data = true) :
    entries.all (fun entry => entry.2.check isBase entry.1) = true := by
  rw [binding] at checked
  simp only [check, List.all_map, Function.comp_def] at checked
  apply List.all_eq_true.mpr
  rintro ⟨known, step⟩ member
  exact (stepCheck_encode isBase known step).symm.trans (List.all_eq_true.mp checked _ member)

def sourceEntries (known : List GKRAddress) : FunctionalProgram → List (List GKRAddress × FunctionalStep)
  | [] => []
  | step :: rest => (known, step) :: sourceEntries (step.outputs ++ known) rest

def fillKnown (known : List Nat) : List Data → List Data
  | [] => []
  | step :: rest => {step with known} :: fillKnown (step.outputs.map Prod.fst ++ known) rest

theorem fillKnown_binding (isBase : GKRAddress → Bool) (known : List GKRAddress)
    (program : FunctionalProgram) :
    fillKnown (known.map AddressUniqueChecks.addressCode)
      (program.map (fun step => encode isBase ([], step))) =
      (sourceEntries known program).map (encode isBase) := by
  induction program generalizing known with
  | nil => rfl
  | cons step rest ih =>
      simp only [List.map_cons, fillKnown, sourceEntries]
      congr 1
      simpa only [encode, List.map_map, Function.comp_def, port, List.map_append] using
        ih (step.outputs ++ known)

theorem sourceEntries_check (isBase : GKRAddress → Bool) (known : List GKRAddress)
    (program : FunctionalProgram) :
    (sourceEntries known program).all (fun entry => entry.2.check isBase entry.1) =
      program.check isBase known := by
  induction program generalizing known with
  | nil => rfl
  | cons step rest ih => simp only [sourceEntries, List.all_cons, FunctionalProgram.check, ih]

theorem check_sound_program (isBase : GKRAddress → Bool) (program : FunctionalProgram)
    (ports : List Data) (binding : ports = program.map (fun step => encode isBase ([], step)))
    (checked : check (fillKnown [] ports) = true) : program.check isBase [] = true := by
  have complete : fillKnown [] ports = (sourceEntries [] program).map (encode isBase) := by
    rw [binding]
    exact fillKnown_binding isBase [] program
  have valid := check_sound isBase (sourceEntries [] program) (fillKnown [] ports) complete checked
  exact (sourceEntries_check isBase [] program).symm.trans valid

abbrev Known := Std.TreeSet Nat compare

def treeStepCheck (known : Known) (data : Data) : Bool :=
  distinct (data.outputs.map Prod.fst) &&
    data.outputs.all (fun output => output.2 == 0 && !known.contains output.1) &&
    data.inputs.all (fun input => input.2 == 1 || known.contains input.1)

def treeCheck (known : Known) : List Data → Bool
  | [] => true
  | step :: rest => treeStepCheck known step &&
      treeCheck (known.insertMany (step.outputs.map Prod.fst)) rest

theorem treeStepCheck_encode (isBase : GKRAddress → Bool) (known : List GKRAddress)
    (state : Known) (agrees : ∀ index, state.contains index = (known.map AddressUniqueChecks.addressCode).contains index)
    (step : FunctionalStep) :
    treeStepCheck state (encode isBase ([], step)) = step.check isBase known := by
  rw [← stepCheck_encode isBase known step]
  simp only [treeStepCheck, stepCheck, encode, agrees]

theorem treeCheck_encode (isBase : GKRAddress → Bool) (known : List GKRAddress)
    (program : FunctionalProgram) (state : Known)
    (agrees : ∀ index, state.contains index = (known.map AddressUniqueChecks.addressCode).contains index) :
    treeCheck state (program.map (fun step => encode isBase ([], step))) = program.check isBase known := by
  induction program generalizing known state with
  | nil => rfl
  | cons step rest ih =>
      simp only [List.map_cons, treeCheck, FunctionalProgram.check]
      rw [treeStepCheck_encode isBase known state agrees step]
      congr 1
      apply ih (step.outputs ++ known)
      intro index
      rw [Std.TreeSet.contains_insertMany_list, agrees]
      simp only [encode, List.map_map, Function.comp_def, port, List.map_append, List.contains_append]
      exact Bool.or_comm _ _

theorem tree_check_sound (isBase : GKRAddress → Bool) (program : FunctionalProgram)
    (ports : List Data) (binding : ports = program.map (fun step => encode isBase ([], step)))
    (checked : treeCheck ∅ ports = true) : program.check isBase [] = true := by
  rw [binding] at checked
  have agrees : ∀ index, (∅ : Known).contains index = (([] : List GKRAddress).map AddressUniqueChecks.addressCode).contains index := by
    intro index
    simp only [Std.TreeSet.contains_emptyc, List.map_nil, List.contains_nil]
  rw [treeCheck_encode isBase [] program ∅ agrees] at checked
  exact checked

theorem sourceEntries_length (known : List GKRAddress) (program : FunctionalProgram) :
    (sourceEntries known program).length = program.length := by
  induction program generalizing known with
  | nil => rfl
  | cons step rest ih => simp only [sourceEntries, List.length_cons, ih]

end Airbender.Compiler.NumericFunctionalStepChecks
