module
public import Slop.Trace.RVTransferWindow
public import Slop.Delegation.RVSharedImage
public import Slop.Trace.RVValues

@[expose] public section

/-! RV siblings of the `Transfer.Inputs`-level lemmas (`TransferHistory`, `TransferBounds`, `TransferTerminal`): the
    seeds are an `initialImageRV` of an `RV.State`. Address-domain facts are the state-free `SeedTransfer` ones. -/

namespace Airbender.Trace.Proofs.Transfer
open Arithmetic
set_option warningAsError true

/-- RV sibling of `Inputs`: the seeds are read from an `RV.State`, one per cell. -/
structure RVInputs (data : Data p) (before : RV.State) (cells : List Cell) : Prop where
  initialization : initialImageRV before cells = some data.initial
  distinct : (cells.map Cell.addressCode).Nodup

theorem RVInputs.toRVBoundaryInputs {data : Data p} {before : RV.State} {cells : List Cell}
    (inputs : RVInputs data before cells) : RVBoundaryInputs data before cells :=
  rv_boundary_inputs inputs.initialization inputs.distinct

theorem RVInputs.toSeed {data : Data p} {before : RV.State} {cells : List Cell}
    (inputs : RVInputs data before cells) : SeedTransfer.SeedInputs data cells :=
  inputs.toRVBoundaryInputs.toSeedInputs

theorem rv_produced_bounds {data : Data p} (facts : Facts data)
    {before : RV.State} {cells : List Cell} (inputs : RVInputs data before cells)
    (rules : WriteRules data) :
    ∀ token ∈ data.initial ++ data.steps.map Prod.snd, token.word.Bounded :=
  produced_bounds_of_seed facts (RVValues.rv_image_bounds inputs.initialization) rules

theorem rv_read_bounds {data : Data p} (facts : Facts data)
    {before : RV.State} {cells : List Cell} (inputs : RVInputs data before cells)
    (rules : WriteRules data) : ∀ edge ∈ data.steps, edge.1.word.Bounded := by
  intro edge present
  exact rv_produced_bounds facts inputs rules edge.1 (facts.matching.mem_iff.mpr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, present, rfl⟩))))

theorem rv_terminal_bounds {data : Data p} (facts : Facts data)
    {before : RV.State} {cells : List Cell} (inputs : RVInputs data before cells)
    (rules : WriteRules data) : ∀ token ∈ data.terminal, token.word.Bounded := by
  intro token present
  exact rv_produced_bounds facts inputs rules token
    (facts.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl present)))

end Airbender.Trace.Proofs.Transfer

namespace Airbender.Trace.Proofs.Transfer
open Arithmetic

theorem RVInputs.toRVNativeInputs {data : Data p} {before : RV.State} {cells : List Cell}
    (inputs : RVInputs data before cells) : RVNativeInputs data before cells :=
  ⟨inputs.toRVBoundaryInputs, RVValues.rv_image_bounds inputs.initialization,
    Transfer.rv_image_clocks inputs.initialization⟩

end Airbender.Trace.Proofs.Transfer
