//! Which `(layer, regime)` coordinates the backward VM computes.
//!
//! A backward coordinate is a `(layer, regime)` pair, not a layer: `R0` and
//! `Ext` are different programs over the same layer, compiled by different
//! ordering passes ([`compile_lean_coordinate`] orders terms at R0 and atoms in
//! `Ext`). So the switch names pairs, and `0:R0` is a different selection from
//! `0:Ext`.
//!
//! [`compile_lean_coordinate`]: gkr_eval_isa::bwd::coeff::lean_artifact::compile_lean_coordinate

use std::fmt;

use crate::upstream::BwdRegime;

/// Env var naming the coordinates the backward VM runs, as a comma-separated
/// `layer:regime` list (`AB_GKR_BWD_VM_COORDS="0:R0"`). UNSET means every
/// coordinate this circuit compiled; an explicit EMPTY value means none.
pub(crate) const AB_GKR_BWD_VM_COORDS_ENV: &str = "AB_GKR_BWD_VM_COORDS";

/// One `(layer, regime)` coordinate.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct BwdVmCoord {
    pub(crate) layer: usize,
    pub(crate) regime: BwdRegime,
}

impl fmt::Display for BwdVmCoord {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let regime = match self.regime {
            BwdRegime::R0 => "R0",
            BwdRegime::Ext => "Ext",
        };
        write!(f, "{}:{regime}", self.layer)
    }
}

/// Why a coordinate selection was rejected. Every variant is an operator error
/// in the switch, not a runtime condition.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum BwdVmCoordError {
    /// An entry is not `layer:regime`.
    Malformed { value: String, entry: String },
    /// The same coordinate appears twice.
    Duplicate { coord: BwdVmCoord },
    /// The coordinate parses but has no binder in this slice.
    NotWired { coord: BwdVmCoord },
    /// Only one regime of a layer was selected. A VM-owned layer must be owned
    /// whole; see [`check_selection`].
    HalfLayer {
        coord: BwdVmCoord,
        missing: BwdVmCoord,
    },
}

impl fmt::Display for BwdVmCoordError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BwdVmCoordError::Malformed { value, entry } => write!(
                f,
                "{AB_GKR_BWD_VM_COORDS_ENV}={value:?} is not a comma-separated `layer:regime` \
                 list: {entry:?} is not a coordinate (regime is `R0` or `Ext`)"
            ),
            BwdVmCoordError::Duplicate { coord } => write!(
                f,
                "{AB_GKR_BWD_VM_COORDS_ENV} names coordinate {coord} more than once"
            ),
            BwdVmCoordError::NotWired { coord } => write!(
                f,
                "{AB_GKR_BWD_VM_COORDS_ENV} selects {coord}, whose layer index is not a main \
                 layer of any circuit the VM supports"
            ),
            BwdVmCoordError::HalfLayer { coord, missing } => write!(
                f,
                "{AB_GKR_BWD_VM_COORDS_ENV} selects {coord} without {missing}: a VM-owned layer \
                 must be owned whole, because the VM owns its own fold buffers and a flat round \
                 of the same layer would have nowhere agreed to write them"
            ),
        }
    }
}

/// The largest main-layer count of any circuit the VM supports — add_sub has 4,
/// blake2_with_extended_control has 8. A parse-time bound only: whether a layer is
/// actually runnable is per circuit, and
/// [`check_vm_selection_is_servable`](crate::prover::gkr::check_vm_selection_is_servable)
/// decides it against the programs that circuit actually compiled, before anything
/// is enqueued.
///
/// This exists so a typo like `9:R0` fails when the switch is parsed rather than
/// later; it deliberately does NOT claim every layer below it runs everywhere.
pub(crate) const MAX_WIRED_LAYERS: usize = 8;

pub(crate) fn coord_is_wired(coord: BwdVmCoord) -> bool {
    coord.layer < MAX_WIRED_LAYERS
}

/// Reject a selection naming anything this slice cannot run, or naming only one
/// regime of a layer.
///
/// A selected layer must be VM-owned WHOLE — both `R0` and `Ext`. The two used to
/// select independently, and that flexibility is what forced the VM to bind its
/// fold buffers out of the flat path's per-layer map: with round 0 flat and round 1
/// on the VM, the flat kernel writes the buffer the VM's first continuation round
/// reads, so both arms have to name the same allocation.
///
/// Owning the layer outright lets the VM own those buffers instead — created just
/// before the round whose prologue writes them and dropped once the next fold has
/// consumed them — which is both a smaller live set and the reason a source the
/// flat path never folds at this layer is no longer unbindable.
pub(crate) fn check_selection(coords: &[BwdVmCoord]) -> Result<(), BwdVmCoordError> {
    for &coord in coords {
        if !coord_is_wired(coord) {
            return Err(BwdVmCoordError::NotWired { coord });
        }
    }
    for &coord in coords {
        let mate = BwdVmCoord {
            layer: coord.layer,
            regime: match coord.regime {
                BwdRegime::R0 => BwdRegime::Ext,
                BwdRegime::Ext => BwdRegime::R0,
            },
        };
        if !coords.contains(&mate) {
            return Err(BwdVmCoordError::HalfLayer { coord, missing: mate });
        }
    }
    Ok(())
}

/// The selection from the environment, validated.
///
/// Read fresh on every backward pass, NOT cached in a `OnceLock`: the A/B
/// alternates VM-on and VM-off proofs inside one process, and a cached read
/// would freeze whichever arm ran first — silently comparing an arm against
/// itself. Same reason `forward::path::vm_layers_from_env` is uncached.
///
/// A malformed or unwired value panics rather than degrading to an empty
/// selection, so a typo cannot look like "the VM was not asked for".
///
/// `None` means the variable is UNSET, which is not "no VM" — it is "whatever
/// this circuit can serve", resolved against the compiled programs by
/// `bwd_vm_slice`. Turning the VM off is an explicit EMPTY value, which is what
/// the A/B harness sets for its off arm; the distinction is the whole reason
/// this returns an `Option` rather than a possibly-empty `Vec`.
pub(crate) fn coords_from_env() -> Option<Vec<BwdVmCoord>> {
    selection_from_value(std::env::var(AB_GKR_BWD_VM_COORDS_ENV).ok().as_deref())
}

/// The env read, factored out so the UNSET/EMPTY distinction is testable without
/// mutating the process environment — which the VM gates read on every pass, so a
/// test that set it would race them.
fn selection_from_value(value: Option<&str>) -> Option<Vec<BwdVmCoord>> {
    let coords = parse_coords(value?).unwrap_or_else(|err| panic!("{err}"));
    check_selection(&coords).unwrap_or_else(|err| panic!("{err}"));
    Some(coords)
}

fn parse_coords(value: &str) -> Result<Vec<BwdVmCoord>, BwdVmCoordError> {
    let mut coords: Vec<BwdVmCoord> = Vec::new();
    for entry in value.split(',').map(str::trim).filter(|e| !e.is_empty()) {
        let malformed = || BwdVmCoordError::Malformed {
            value: value.to_string(),
            entry: entry.to_string(),
        };
        let (layer, regime) = entry.split_once(':').ok_or_else(malformed)?;
        let layer = layer.trim().parse::<usize>().map_err(|_| malformed())?;
        let regime = match regime.trim() {
            "R0" => BwdRegime::R0,
            "Ext" => BwdRegime::Ext,
            _ => return Err(malformed()),
        };
        let coord = BwdVmCoord { layer, regime };
        if coords.contains(&coord) {
            return Err(BwdVmCoordError::Duplicate { coord });
        }
        coords.push(coord);
    }
    Ok(coords)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// UNSET and EMPTY are different answers, and the whole default-on switch
    /// rests on it: unset means "everything this circuit compiled", empty means
    /// "nothing", which is how the A/B harness runs its off arm.
    #[test]
    fn unset_is_the_default_and_empty_is_off() {
        assert_eq!(selection_from_value(None), None, "unset defers to availability");
        assert_eq!(
            selection_from_value(Some("")),
            Some(Vec::new()),
            "an explicit empty value selects nothing"
        );
        assert_eq!(
            selection_from_value(Some("   ")),
            Some(Vec::new()),
            "whitespace is still an explicit nothing"
        );
        assert_eq!(
            selection_from_value(Some("1:R0,1:Ext")),
            Some(vec![r0(1), ext(1)]),
            "an explicit selection is taken verbatim"
        );
    }

    fn r0(layer: usize) -> BwdVmCoord {
        BwdVmCoord {
            layer,
            regime: BwdRegime::R0,
        }
    }

    fn ext(layer: usize) -> BwdVmCoord {
        BwdVmCoord {
            layer,
            regime: BwdRegime::Ext,
        }
    }

    #[test]
    fn a_coord_list_parses_layer_and_regime() {
        assert_eq!(parse_coords("0:R0"), Ok(vec![r0(0)]));
        assert_eq!(
            parse_coords(" 0:R0 , 2:Ext "),
            Ok(vec![
                r0(0),
                BwdVmCoord {
                    layer: 2,
                    regime: BwdRegime::Ext
                },
            ])
        );
        assert_eq!(parse_coords(""), Ok(vec![]));
        assert_eq!(parse_coords("   "), Ok(vec![]));
    }

    /// Unset means "no coordinates"; a value that does not parse is an operator
    /// error and must not be read as "the VM was not asked for".
    #[test]
    fn a_coord_list_that_does_not_parse_is_an_error_not_an_empty_selection() {
        assert!(parse_coords("0").is_err(), "no regime");
        assert!(parse_coords("0:R1").is_err(), "R1 is a round, not a regime");
        assert!(parse_coords("x:R0").is_err());
        assert!(parse_coords("0:").is_err());
        assert!(parse_coords(":R0").is_err());
        assert!(parse_coords("-1:R0").is_err());
    }

    /// A repeated coordinate is a malformed selection, not a doubled launch.
    #[test]
    fn a_repeated_coordinate_is_rejected() {
        assert!(parse_coords("0:R0,0:R0").is_err());
    }

    /// Both regimes of layer 0 are wired. The bound — that a layer past the
    /// circuit's main layers is NOT wired, so it fails loudly rather than
    /// reaching a binder that does not exist for it — is
    /// `every_main_layer_is_wired_in_both_regimes`.
    #[test]
    fn both_regimes_of_layer_zero_are_wired() {
        assert!(coord_is_wired(r0(0)));
        assert!(coord_is_wired(ext(0)));
    }

    #[test]
    fn an_unwired_coordinate_is_rejected_with_the_coordinate_named() {
        let err = check_selection(&[r0(MAX_WIRED_LAYERS)]).unwrap_err();
        assert!(
            format!("{err}").contains(&format!("{}:R0", MAX_WIRED_LAYERS)),
            "got: {err}"
        );
    }

    /// Every layer index inside the parse-time bound is accepted in both regimes;
    /// whether a given circuit can actually RUN one is decided per circuit by
    /// `check_vm_selection_is_servable`.
    #[test]
    fn every_main_layer_is_wired_in_both_regimes() {
        for layer in 0..MAX_WIRED_LAYERS {
            assert!(coord_is_wired(r0(layer)), "layer {layer} R0");
            assert!(coord_is_wired(ext(layer)), "layer {layer} Ext");
        }
        assert!(!coord_is_wired(r0(MAX_WIRED_LAYERS)));
        assert!(!coord_is_wired(ext(MAX_WIRED_LAYERS)));
    }

    #[test]
    fn a_wired_selection_is_accepted() {
        assert!(check_selection(&[]).is_ok());
        assert!(check_selection(&[r0(0), ext(0)]).is_ok());
        assert!(check_selection(&[r0(0), ext(0), r0(1), ext(1)]).is_ok());
    }

    /// Half a layer is not a selection. `r0(0)` alone used to be accepted — the two
    /// regimes selected independently — and is now rejected because a VM-owned layer
    /// owns its own fold buffers, which a flat round of the same layer could not
    /// share.
    #[test]
    fn a_half_owned_layer_is_rejected() {
        assert!(matches!(
            check_selection(&[r0(0)]),
            Err(BwdVmCoordError::HalfLayer { .. })
        ));
        assert!(matches!(
            check_selection(&[ext(0)]),
            Err(BwdVmCoordError::HalfLayer { .. })
        ));
        // One whole layer plus half of another is still a rejection.
        assert!(matches!(
            check_selection(&[r0(0), ext(0), ext(1)]),
            Err(BwdVmCoordError::HalfLayer { .. })
        ));
    }

    /// The full-layer selection the Ext parity gates run under.
    #[test]
    fn the_combined_r0_and_ext_selection_parses_and_is_wired() {
        let coords = parse_coords("0:R0,0:Ext").unwrap();
        assert_eq!(coords, vec![r0(0), ext(0)]);
        assert!(check_selection(&coords).is_ok());
    }
}
