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
/// `layer:regime` list (`AB_GKR_BWD_VM_COORDS="0:R0"`). Unset means none.
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
                "{AB_GKR_BWD_VM_COORDS_ENV} selects {coord}, which has no production binder; \
                 only 0:R0 and 0:Ext are wired"
            ),
        }
    }
}

/// The coordinates this slice can actually run. Deliberately a hard list rather
/// than a predicate over the artifact: a coordinate reaching a binder that was
/// never built for it must stop the proof, not launch something shaped wrong.
const WIRED_COORDS: [BwdVmCoord; 2] = [
    BwdVmCoord {
        layer: 0,
        regime: BwdRegime::R0,
    },
    BwdVmCoord {
        layer: 0,
        regime: BwdRegime::Ext,
    },
];

pub(crate) fn coord_is_wired(coord: BwdVmCoord) -> bool {
    WIRED_COORDS.contains(&coord)
}

/// Reject a selection naming anything this slice cannot run.
pub(crate) fn check_selection(coords: &[BwdVmCoord]) -> Result<(), BwdVmCoordError> {
    for &coord in coords {
        if !coord_is_wired(coord) {
            return Err(BwdVmCoordError::NotWired { coord });
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
pub(crate) fn coords_from_env() -> Vec<BwdVmCoord> {
    let coords = match std::env::var(AB_GKR_BWD_VM_COORDS_ENV) {
        Ok(value) => parse_coords(&value).unwrap_or_else(|err| panic!("{err}")),
        Err(_) => Vec::new(),
    };
    check_selection(&coords).unwrap_or_else(|err| panic!("{err}"));
    coords
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

    /// Both regimes of layer 0 are wired — and nothing else. Anything else must
    /// fail loudly rather than reach a binder that does not exist for it.
    #[test]
    fn both_regimes_of_layer_zero_are_wired() {
        assert!(coord_is_wired(r0(0)));
        assert!(coord_is_wired(ext(0)));
        assert!(!coord_is_wired(r0(1)));
        assert!(!coord_is_wired(ext(1)));
    }

    #[test]
    fn an_unwired_coordinate_is_rejected_with_the_coordinate_named() {
        let err = check_selection(&[r0(1)]).unwrap_err();
        assert!(format!("{err}").contains("1:R0"), "got: {err}");
    }

    #[test]
    fn a_wired_selection_is_accepted() {
        assert!(check_selection(&[]).is_ok());
        assert!(check_selection(&[r0(0)]).is_ok());
        assert!(check_selection(&[r0(0), ext(0)]).is_ok());
    }

    /// The full-layer selection the Ext parity gates run under.
    #[test]
    fn the_combined_r0_and_ext_selection_parses_and_is_wired() {
        let coords = parse_coords("0:R0,0:Ext").unwrap();
        assert_eq!(coords, vec![r0(0), ext(0)]);
        assert!(check_selection(&coords).is_ok());
    }
}
