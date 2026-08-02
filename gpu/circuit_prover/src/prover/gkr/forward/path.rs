//! Which code path computes each forward layer.
//!
//! The forward pass has more than one implementation of a layer: the flat plan
//! it has always had, the pre-generated fused layer-0 kernel
//! ([`super::generated_layer0`]), and the interpreter VM ([`super::vm`]). Each
//! is selected by its own env var, and each *replaces* the flat scheduling for
//! the layers it claims. Two independent booleans would let two of them claim
//! layer 0, with whichever branch is tested first silently winning — so the
//! selection is resolved once, up front, into exactly one [`ForwardPath`] per
//! layer, and an overlap is an error rather than a precedence rule.

use std::fmt;
use std::sync::OnceLock;

/// Env var naming the layers the forward interpreter VM runs: a comma-separated
/// list of layer indices (`AB_GKR_FWD_VM_LAYERS=0`). Unset means no VM layers.
pub(crate) const AB_GKR_FWD_VM_LAYERS_ENV: &str = "AB_GKR_FWD_VM_LAYERS";

/// The implementation that computes one forward layer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ForwardPath {
    /// The default: cache relations, materialized lookup inputs, flat plan.
    Flat,
    /// The pre-generated fused add_sub layer-0 kernel.
    GeneratedLayer0,
    /// The forward interpreter VM.
    Vm,
}

impl fmt::Display for ForwardPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            ForwardPath::Flat => "flat",
            ForwardPath::GeneratedLayer0 => "generated-layer0",
            ForwardPath::Vm => "vm",
        };
        f.write_str(name)
    }
}

/// Why a path selection could not be resolved. Every variant is an operator
/// error in the switch env vars, not a runtime condition.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum ForwardPathError {
    /// Two switches named the same layer.
    Conflict {
        layer: usize,
        claimed: ForwardPath,
        also_claimed_by: ForwardPath,
    },
    /// A selected layer is outside the circuit.
    OutOfRange { layer: usize, total_layers: usize },
    /// `AB_GKR_FWD_VM_LAYERS` did not parse as a layer list.
    Malformed { value: String, entry: String },
}

impl fmt::Display for ForwardPathError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ForwardPathError::Conflict {
                layer,
                claimed,
                also_claimed_by,
            } => write!(
                f,
                "forward layer {layer} is claimed by the {claimed} path and also by the \
                 {also_claimed_by} path; exactly one path may compute a layer"
            ),
            ForwardPathError::OutOfRange {
                layer,
                total_layers,
            } => write!(
                f,
                "forward layer {layer} was selected but the circuit has only {total_layers} layers"
            ),
            ForwardPathError::Malformed { value, entry } => write!(
                f,
                "{AB_GKR_FWD_VM_LAYERS_ENV}={value:?} is not a comma-separated layer list: \
                 {entry:?} is not a layer index"
            ),
        }
    }
}

/// One resolved [`ForwardPath`] per layer of the circuit.
#[derive(Debug)]
pub(crate) struct ForwardPaths {
    paths: Vec<ForwardPath>,
}

impl ForwardPaths {
    pub(crate) fn path(&self, layer: usize) -> ForwardPath {
        self.paths[layer]
    }
}

/// Resolve the per-layer path selection, or reject it.
///
/// `generated_layer0_active` and `vm_layers` come from their respective env
/// switches, already filtered by the caller's structural predicate (a switch
/// is never "active" for a circuit its kernel was not built for).
pub(crate) fn plan_forward_paths(
    total_layers: usize,
    generated_layer0_active: bool,
    vm_layers: &[usize],
) -> Result<ForwardPaths, ForwardPathError> {
    let mut paths = vec![ForwardPath::Flat; total_layers];

    let mut claim = |layer: usize, by: ForwardPath| -> Result<(), ForwardPathError> {
        if layer >= total_layers {
            return Err(ForwardPathError::OutOfRange {
                layer,
                total_layers,
            });
        }
        if paths[layer] != ForwardPath::Flat {
            return Err(ForwardPathError::Conflict {
                layer,
                claimed: paths[layer],
                also_claimed_by: by,
            });
        }
        paths[layer] = by;
        Ok(())
    };

    if generated_layer0_active {
        claim(0, ForwardPath::GeneratedLayer0)?;
    }
    for &layer in vm_layers {
        claim(layer, ForwardPath::Vm)?;
    }

    Ok(ForwardPaths { paths })
}

/// The VM layer selection from the environment. Read once, like
/// [`super::generated_layer0::generated_layer0_enabled`]; a malformed value
/// panics rather than degrading to an empty selection, so a typo cannot look
/// like "the VM was not asked for".
pub(crate) fn vm_layers_from_env() -> &'static [usize] {
    static LAYERS: OnceLock<Vec<usize>> = OnceLock::new();
    LAYERS.get_or_init(|| match std::env::var(AB_GKR_FWD_VM_LAYERS_ENV) {
        Ok(value) => parse_vm_layers(&value).unwrap_or_else(|err| panic!("{err}")),
        Err(_) => Vec::new(),
    })
}

fn parse_vm_layers(value: &str) -> Result<Vec<usize>, ForwardPathError> {
    value
        .split(',')
        .map(str::trim)
        .filter(|entry| !entry.is_empty())
        .map(|entry| {
            entry
                .parse::<usize>()
                .map_err(|_| ForwardPathError::Malformed {
                    value: value.to_string(),
                    entry: entry.to_string(),
                })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The reason this module exists: two switches both naming layer 0 must
    /// fail loudly rather than letting one silently win.
    #[test]
    fn generated_layer0_and_vm_layer0_together_is_a_hard_error() {
        let err = plan_forward_paths(4, true, &[0]).unwrap_err();
        assert_eq!(
            err,
            ForwardPathError::Conflict {
                layer: 0,
                claimed: ForwardPath::GeneratedLayer0,
                also_claimed_by: ForwardPath::Vm,
            }
        );
    }

    #[test]
    fn unselected_layers_are_flat() {
        let paths = plan_forward_paths(4, false, &[0]).unwrap();
        assert_eq!(paths.path(0), ForwardPath::Vm);
        assert_eq!(paths.path(1), ForwardPath::Flat);
        assert_eq!(paths.path(3), ForwardPath::Flat);
    }

    #[test]
    fn generated_layer0_alone_still_owns_layer_zero() {
        let paths = plan_forward_paths(4, true, &[]).unwrap();
        assert_eq!(paths.path(0), ForwardPath::GeneratedLayer0);
        assert_eq!(paths.path(1), ForwardPath::Flat);
    }

    /// A typo in `AB_GKR_FWD_VM_LAYERS` must not silently select nothing.
    #[test]
    fn a_vm_layer_outside_the_circuit_is_rejected() {
        let err = plan_forward_paths(4, false, &[4]).unwrap_err();
        assert_eq!(
            err,
            ForwardPathError::OutOfRange {
                layer: 4,
                total_layers: 4,
            }
        );
    }

    #[test]
    fn a_repeated_vm_layer_is_rejected() {
        let err = plan_forward_paths(4, false, &[2, 2]).unwrap_err();
        assert_eq!(
            err,
            ForwardPathError::Conflict {
                layer: 2,
                claimed: ForwardPath::Vm,
                also_claimed_by: ForwardPath::Vm,
            }
        );
    }

    #[test]
    fn the_layer_list_parses_a_comma_separated_selection() {
        assert_eq!(parse_vm_layers("0"), Ok(vec![0]));
        assert_eq!(parse_vm_layers(" 0 , 2 "), Ok(vec![0, 2]));
        assert_eq!(parse_vm_layers(""), Ok(vec![]));
        assert_eq!(parse_vm_layers("   "), Ok(vec![]));
    }

    /// Unset means "no VM layers"; a value that does not parse is an operator
    /// error and must not be read as "no VM layers".
    #[test]
    fn a_layer_list_that_does_not_parse_is_an_error_not_an_empty_selection() {
        assert!(parse_vm_layers("0,x").is_err());
        assert!(parse_vm_layers("-1").is_err());
        assert!(parse_vm_layers("true").is_err());
    }
}
