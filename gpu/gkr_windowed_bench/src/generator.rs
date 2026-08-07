use std::path::Path;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_ir::FieldKind;
use gpu_gkr_compiler::backward::{
    decode_continuation_program, LeanAtom, LeanSourceBinding, LeanTerm, WindowFamily,
};
use gpu_gkr_compiler::{compile_continuations, GpuResourceProfile};

use crate::abi::WindowInstruction;
use crate::artifact::{
    encode_artifact, validate_artifact, FrozenArtifact, FrozenBoundColumn, FrozenField,
    FrozenSourceSlot, FrozenWindow, FrozenWindowFamily, WindowClass, ARTIFACT_MAGIC,
    ARTIFACT_VERSION, SOURCE_NONE,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratorError(String);

impl GeneratorError {
    fn context(context: &str, error: impl core::fmt::Display) -> Self {
        Self(format!("{context}: {error}"))
    }
}

impl core::fmt::Display for GeneratorError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for GeneratorError {}

pub fn generate_add_sub_layer0(layout_path: &Path) -> Result<FrozenArtifact, GeneratorError> {
    let bytes = std::fs::read(layout_path)
        .map_err(|error| GeneratorError::context("read circuit layout", error))?;
    let circuit: GKRCircuitArtifact<BabyBearField> = serde_json::from_slice(&bytes)
        .map_err(|error| GeneratorError::context("parse circuit layout", error))?;
    let dag = gkr_eval_ir::lower_dag(&circuit)
        .map_err(|error| GeneratorError::context("lower circuit DAG", error))?;
    gkr_eval_ir::validate(&dag)
        .map_err(|error| GeneratorError::context("validate circuit DAG", error))?;
    let bundle = compile_continuations(&dag, &GpuResourceProfile::production())
        .map_err(|error| GeneratorError::context("compile full continuation relation", error))?;
    let layer = bundle
        .layers
        .into_iter()
        .find(|layer| layer.layer == 0)
        .ok_or_else(|| GeneratorError("compiled program has no layer 0".to_owned()))?;
    let atoms = decode_continuation_program(&layer.program)
        .map_err(|error| GeneratorError(format!("decode continuation program: {error:?}")))?;

    let mut program = Vec::with_capacity(layer.program.words.len() / 4);
    for atom in atoms {
        match atom {
            LeanAtom::Term(term) => {
                program.push(encode_term(&term, &layer.binding)?);
            }
            LeanAtom::Group {
                core,
                has_c0: _,
                has_c2: _,
                members,
            } => {
                let member_count = u16::try_from(members.len())
                    .map_err(|error| GeneratorError::context("group member count", error))?;
                let encoded_members = members
                    .iter()
                    .map(|member| encode_term(member, &layer.binding))
                    .collect::<Result<Vec<_>, GeneratorError>>()?;
                let all_bf = encoded_members.iter().all(|record| {
                    matches!(
                        record_class(record),
                        WindowClass::LinearBf | WindowClass::ProductBfBf
                    )
                });
                let all_e4 = encoded_members.iter().all(|record| {
                    matches!(
                        record_class(record),
                        WindowClass::LinearE4 | WindowClass::ProductBfE4 | WindowClass::ProductE4E4
                    )
                });
                let group_class = if all_bf && member_count >= 2 {
                    WindowClass::GroupBf
                } else if all_e4
                    && member_count == 2
                    && encoded_members.iter().all(|record| record.factor < 2)
                {
                    WindowClass::GroupE4
                } else {
                    return Err(GeneratorError(format!(
                        "unsupported round-0 group: members={} all_bf={all_bf} all_e4={all_e4}",
                        members.len()
                    )));
                };
                let encoded_count = if group_class == WindowClass::GroupBf {
                    member_count
                } else {
                    0
                };
                program.push(WindowInstruction {
                    term_class: group_class as u16,
                    factor: core,
                    source_a: encoded_count,
                    source_b: 0,
                });
                program.extend(encoded_members);
            }
        }
    }

    let windows = layer
        .binding
        .windows
        .iter()
        .map(|window| {
            let first_column = u32::try_from(window.first_column)
                .map_err(|error| GeneratorError::context("window first column", error))?;
            let field = match window.backing_field() {
                FieldKind::Base => FrozenField::Base,
                FieldKind::Ext => FrozenField::Ext,
            };
            let columns = window
                .columns
                .iter()
                .map(|column| {
                    Ok(FrozenBoundColumn {
                        column: u32::try_from(column.column).map_err(|error| {
                            GeneratorError::context("bound source column", error)
                        })?,
                        source: column.source,
                    })
                })
                .collect::<Result<Vec<_>, GeneratorError>>()?;
            Ok(FrozenWindow {
                family: convert_family(window.family)?,
                first_column,
                field,
                columns,
            })
        })
        .collect::<Result<Vec<_>, GeneratorError>>()?;
    let source_slots = layer
        .binding
        .source_slots
        .iter()
        .map(|slot| FrozenSourceSlot {
            window: slot.window,
            column: slot.column,
        })
        .collect();
    let coefficient_count = u32::try_from(layer.coefficients.coefficients.len())
        .map_err(|error| GeneratorError::context("coefficient count", error))?
        .checked_add(2)
        .ok_or_else(|| GeneratorError("coefficient count overflow".to_owned()))?;
    let artifact = FrozenArtifact {
        magic: ARTIFACT_MAGIC,
        version: ARTIFACT_VERSION,
        layer: 0,
        term_count: u32::try_from(layer.program.term_count)
            .map_err(|error| GeneratorError::context("term count", error))?,
        record_count: u32::try_from(program.len())
            .map_err(|error| GeneratorError::context("record count", error))?,
        coefficient_count,
        c_init_coeff: layer.coefficients.c_init.map(|coefficient| coefficient.0),
        program,
        immediates: layer.coefficients.immediates,
        windows,
        source_slots,
    };
    validate_artifact(&artifact)
        .map_err(|error| GeneratorError::context("validate frozen artifact", error))?;
    Ok(artifact)
}

pub fn generate_bytes(layout_path: &Path) -> Result<Vec<u8>, GeneratorError> {
    let artifact = generate_add_sub_layer0(layout_path)?;
    encode_artifact(&artifact)
        .map_err(|error| GeneratorError::context("encode frozen artifact", error))
}

fn encode_term(
    term: &LeanTerm,
    binding: &LeanSourceBinding,
) -> Result<WindowInstruction, GeneratorError> {
    let class = match term.class {
        0 => match source_field(binding, term.source_a)? {
            FrozenField::Base => WindowClass::LinearBf,
            FrozenField::Ext => WindowClass::LinearE4,
        },
        1 => {
            let field_a = source_field(binding, term.source_a)?;
            let field_b = source_field(binding, term.source_b)?;
            match (field_a, field_b) {
                (FrozenField::Base, FrozenField::Base) => WindowClass::ProductBfBf,
                (FrozenField::Base, FrozenField::Ext) | (FrozenField::Ext, FrozenField::Base) => {
                    WindowClass::ProductBfE4
                }
                (FrozenField::Ext, FrozenField::Ext) => WindowClass::ProductE4E4,
            }
        }
        class => {
            return Err(GeneratorError(format!(
                "continuation term uses unsupported class {class}"
            )));
        }
    };
    let (source_a, source_b) = if class == WindowClass::ProductBfE4
        && source_field(binding, term.source_a)? == FrozenField::Ext
    {
        (term.source_b, term.source_a)
    } else {
        (term.source_a, term.source_b)
    };
    Ok(WindowInstruction {
        term_class: class as u16,
        factor: term.coeff,
        source_a,
        source_b,
    })
}

fn record_class(record: &WindowInstruction) -> WindowClass {
    WindowClass::try_from(record.term_class as u8)
        .expect("encode_term always emits a known term class")
}

fn source_field(binding: &LeanSourceBinding, source: u16) -> Result<FrozenField, GeneratorError> {
    if source == SOURCE_NONE {
        return Err(GeneratorError("product source is absent".to_owned()));
    }
    let slot = binding
        .source_slots
        .get(usize::from(source))
        .ok_or_else(|| GeneratorError(format!("source {source} is out of range")))?;
    let window = binding
        .windows
        .get(usize::from(slot.window))
        .ok_or_else(|| GeneratorError(format!("source {source} window is out of range")))?;
    Ok(match window.backing_field() {
        FieldKind::Base => FrozenField::Base,
        FieldKind::Ext => FrozenField::Ext,
    })
}

fn convert_family(family: WindowFamily) -> Result<FrozenWindowFamily, GeneratorError> {
    Ok(match family {
        WindowFamily::BaseLayerMemory => FrozenWindowFamily::BaseLayerMemory,
        WindowFamily::BaseLayerWitness => FrozenWindowFamily::BaseLayerWitness,
        WindowFamily::Setup => FrozenWindowFamily::Setup,
        WindowFamily::Scratch => FrozenWindowFamily::Scratch,
        WindowFamily::LayerOutput { layer, ext } => FrozenWindowFamily::LayerOutput {
            layer: u32::try_from(layer)
                .map_err(|error| GeneratorError::context("layer output index", error))?,
            ext,
        },
        WindowFamily::CacheOutput { layer, ext } => FrozenWindowFamily::CacheOutput {
            layer: u32::try_from(layer)
                .map_err(|error| GeneratorError::context("cache output index", error))?,
            ext,
        },
        WindowFamily::VirtualSetup { kind } => FrozenWindowFamily::VirtualSetup { kind },
    })
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use crate::artifact::{decode_program, validate_artifact, WindowAtom};

    use super::*;

    fn add_sub_layout() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json")
    }

    #[test]
    fn add_sub_layer_zero_generates_a_complete_portable_program() {
        let artifact = generate_add_sub_layer0(&add_sub_layout()).unwrap();
        let stats = validate_artifact(&artifact).unwrap();
        let (atoms, decoded) = decode_program(&artifact).unwrap();

        assert_eq!(artifact.layer, 0);
        assert!(artifact.term_count > 0);
        assert!(artifact.coefficient_count > 2);
        assert!(!artifact.program.is_empty());
        assert!(!artifact.source_slots.is_empty());
        assert!(!artifact.windows.is_empty());
        assert_eq!(stats, decoded);
        assert_eq!(decoded.terms, artifact.term_count);
        assert!(atoms.iter().all(|atom| match atom {
            WindowAtom::Term(_) => true,
            WindowAtom::GroupBf { members, .. } | WindowAtom::GroupE4 { members, .. } => {
                members.len() >= 2
            }
        }));
        assert_eq!(decoded.bf_groups, 23);
        assert_eq!(decoded.e4_groups, 2);
    }

    #[test]
    fn add_sub_layer_zero_generation_is_deterministic() {
        let first = generate_add_sub_layer0(&add_sub_layout()).unwrap();
        let second = generate_add_sub_layer0(&add_sub_layout()).unwrap();
        assert_eq!(first, second);
    }
}
