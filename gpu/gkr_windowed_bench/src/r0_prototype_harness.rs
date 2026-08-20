use std::collections::BTreeMap;
use std::fmt;
use std::sync::OnceLock;

use era_cudart::device::{device_get_attribute, get_device};
use era_cudart_sys::CudaDeviceAttr;
use field::{Field, FieldExtension, PrimeField};
use gpu_gkr_compiler::backward::analyze_coeff_grouping;
use serde::{Deserialize, Serialize};

use crate::abi::{BF, E4};
use crate::accumulator_schedule::build_schedule_views;
use crate::census::compile_corpus;
use crate::r0_abi::R0_COEFFICIENT_CAPACITY;
use crate::r0_artifact::FrozenR0Coordinate;
use crate::r0_harness::{R0Harness, R0Observed, R0TimedSession, R0TimingConfig};
use crate::r0_input::{resolve_r0_coefficients, FrozenChallengeBase, ResolvedR0Input};
use crate::r0_prototype_abi::{
    build_dedicated_grouped_descriptor, build_dedicated_sectioned_descriptor,
    build_prototype_descriptors, DedicatedCoefficientPlan, PreparedPrototypeDescriptor,
    R0PrototypePayload,
};
use crate::r0_prototype_encoding::{build_r0_prototype_program_set, R0PrototypeProgramSet};
use crate::r0_prototype_kernels::{
    configure_materialized_shared_memory, launch_r0_prototype, launch_r0_sectioned,
    r0_sectioned_base_geometry, R0SectionedShapePolicy,
};
use crate::r0_prototype_manifest::{
    build_r0_prototype_manifest, r0_sectioned_compatible_compiled_shapes,
    resolve_r0_sectioned_compiled_shape, R0CandidateSymbolV1, R0MeasurementConfigV1,
    R0ProgramEncoding, R0PrototypeManifestV1, R0SectionedGeometry, R0SectionedManifestV1,
    R0SectionedSymbolV1, R0SourcePolicy,
};
use crate::r0_prototype_tile::R0TileCapacity;

pub(crate) fn resolve_dedicated_coefficient_plans(
    plans: &[DedicatedCoefficientPlan],
    challenge_bases: &[FrozenChallengeBase],
) -> Result<Vec<E4>, R0PrototypeHarnessError> {
    plans
        .iter()
        .map(|plan| {
            let recipe = match plan {
                DedicatedCoefficientPlan::Direct(recipe)
                | DedicatedCoefficientPlan::Scaled { recipe, .. }
                | DedicatedCoefficientPlan::LinearBasis { recipe, .. } => recipe,
            };
            let mut value = resolve_r0_coefficients(core::slice::from_ref(recipe), challenge_bases)
                .map_err(|error| {
                    R0PrototypeHarnessError(format!(
                        "resolve dedicated coefficient plan: {error:?}"
                    ))
                })?
                .into_iter()
                .next()
                .ok_or_else(|| {
                    R0PrototypeHarnessError(
                        "resolved dedicated coefficient plan is empty".to_owned(),
                    )
                })?;
            match plan {
                DedicatedCoefficientPlan::Direct(_) => {}
                DedicatedCoefficientPlan::Scaled { scalar, .. } => {
                    value.mul_assign(&<E4 as FieldExtension<BF>>::from_base(
                        BF::from_u32_with_reduction(*scalar),
                    ));
                }
                DedicatedCoefficientPlan::LinearBasis { limb, .. } => {
                    let mut basis = [BF::ZERO; 4];
                    let slot = basis.get_mut(usize::from(*limb)).ok_or_else(|| {
                        R0PrototypeHarnessError(format!(
                            "dedicated linear basis limb {limb} is out of range"
                        ))
                    })?;
                    *slot = BF::ONE;
                    value.mul_assign(&E4::from_array_of_base(basis));
                }
            }
            Ok(value)
        })
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0PrototypeDeviceCapacity {
    pub default_shared_bytes: u32,
    pub opt_in_shared_bytes: u32,
}

impl R0PrototypeDeviceCapacity {
    pub fn query() -> Result<Self, R0PrototypeHarnessError> {
        let device = get_device().map_err(|error| {
            R0PrototypeHarnessError(format!("query current CUDA device: {error:?}"))
        })?;
        let default_shared_bytes =
            device_get_attribute(CudaDeviceAttr::MaxSharedMemoryPerBlock, device).map_err(
                |error| {
                    R0PrototypeHarnessError(format!("query default shared-memory limit: {error:?}"))
                },
            )?;
        let opt_in_shared_bytes =
            device_get_attribute(CudaDeviceAttr::MaxSharedMemoryPerBlockOptin, device).map_err(
                |error| {
                    R0PrototypeHarnessError(format!("query opt-in shared-memory limit: {error:?}"))
                },
            )?;
        Ok(Self {
            default_shared_bytes: u32::try_from(default_shared_bytes).map_err(|_| {
                R0PrototypeHarnessError("negative default shared-memory limit".to_owned())
            })?,
            opt_in_shared_bytes: u32::try_from(opt_in_shared_bytes).map_err(|_| {
                R0PrototypeHarnessError("negative opt-in shared-memory limit".to_owned())
            })?,
        })
    }

    pub const fn classify(self, required_bytes: u32) -> R0PrototypeLaunchability {
        if required_bytes <= self.default_shared_bytes {
            R0PrototypeLaunchability::Launchable {
                dynamic_shared_bytes: required_bytes,
                opt_in: false,
            }
        } else if required_bytes <= self.opt_in_shared_bytes {
            R0PrototypeLaunchability::Launchable {
                dynamic_shared_bytes: required_bytes,
                opt_in: true,
            }
        } else {
            R0PrototypeLaunchability::UnlaunchableCapacity {
                required_bytes,
                device_limit_bytes: self.opt_in_shared_bytes,
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0PrototypeLaunchability {
    Launchable {
        dynamic_shared_bytes: u32,
        opt_in: bool,
    },
    UnlaunchableCapacity {
        required_bytes: u32,
        device_limit_bytes: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0PrototypeHarnessError(String);

impl fmt::Display for R0PrototypeHarnessError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for R0PrototypeHarnessError {}

struct ProgramContext {
    programs: R0PrototypeProgramSet,
    canonical: gkr_eval_ir::DagLayer,
}

type ProgramBank = BTreeMap<(String, u32), ProgramContext>;

static PROGRAM_BANK: OnceLock<Result<ProgramBank, String>> = OnceLock::new();

fn program_bank() -> Result<&'static ProgramBank, R0PrototypeHarnessError> {
    match PROGRAM_BANK.get_or_init(|| {
        let corpus = compile_corpus().map_err(|error| error.to_string())?;
        let bundle = crate::r0_artifact::decode_r0_bundle(crate::r0_artifact::R0_CORPUS_BYTES)
            .map_err(|error| format!("decode R0 bundle: {error:?}"))?;
        let mut programs = BTreeMap::new();
        for layer in &corpus.layers {
            let coordinate = bundle
                .coordinates
                .iter()
                .find(|coordinate| {
                    coordinate.circuit == layer.circuit && coordinate.layer == layer.layer as u32
                })
                .ok_or_else(|| {
                    format!(
                        "missing frozen coordinate {}:{}",
                        layer.circuit, layer.layer
                    )
                })?;
            let grouping = analyze_coeff_grouping(&layer.r0.coefficients)
                .map_err(|error| format!("coefficient grouping: {error:?}"))?;
            let schedules =
                build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &grouping)
                    .map_err(|error| format!("accumulator schedule: {error:?}"))?;
            let program = build_r0_prototype_program_set(
                coordinate,
                &layer.r0.coefficients,
                &schedules,
                &grouping,
            )
            .map_err(|error| format!("prototype program: {error:?}"))?;
            let key = (layer.circuit.clone(), layer.layer as u32);
            if programs
                .insert(
                    key.clone(),
                    ProgramContext {
                        programs: program,
                        canonical: layer.canonical.clone(),
                    },
                )
                .is_some()
            {
                return Err(format!("duplicate compiled coordinate {}:{}", key.0, key.1));
            }
        }
        Ok(programs)
    }) {
        Ok(programs) => Ok(programs),
        Err(error) => Err(R0PrototypeHarnessError(error.clone())),
    }
}

pub struct R0PrototypePayloadCache {
    descriptors: Vec<PreparedPrototypeDescriptor>,
    dedicated_grouped: Box<PreparedPrototypeDescriptor>,
    dedicated_sectioned: Box<PreparedPrototypeDescriptor>,
    coefficient_banks: BTreeMap<R0ProgramEncoding, Vec<E4>>,
    dedicated_sectioned_bank: Vec<E4>,
}

const DEDICATED_GROUPED_CONTROL_ID: &str =
    "r0pb/grouped_slot/u64/u96/cta96_partitioned/ordinary/template";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0PrototypeRunConfig {
    pub candidate: R0CandidateSymbolV1,
    pub measurement: R0MeasurementConfigV1,
}

impl R0PrototypeRunConfig {
    pub fn resolve(
        manifest: &R0PrototypeManifestV1,
        configuration_id: &str,
    ) -> Result<Self, R0PrototypeHarnessError> {
        let measurement = manifest
            .configurations
            .iter()
            .find(|row| row.configuration_id == configuration_id)
            .ok_or_else(|| {
                R0PrototypeHarnessError(format!(
                    "unknown prototype configuration {configuration_id}"
                ))
            })?
            .clone();
        let candidate = manifest
            .symbols
            .iter()
            .find(|row| row.candidate_id == measurement.candidate_id)
            .ok_or_else(|| {
                R0PrototypeHarnessError(format!(
                    "configuration {} has missing candidate {}",
                    measurement.configuration_id, measurement.candidate_id
                ))
            })?
            .clone();
        match (candidate.source_policy, measurement.tile_capacity) {
            (R0SourcePolicy::Ordinary, None)
            | (R0SourcePolicy::Materialized, Some(8 | 16 | 32)) => {}
            _ => {
                return Err(R0PrototypeHarnessError(format!(
                    "configuration {} has invalid source/capacity binding",
                    measurement.configuration_id
                )));
            }
        }
        Ok(Self {
            candidate,
            measurement,
        })
    }
}

pub struct R0PrototypeHarness {
    base: R0Harness,
    payloads: R0PrototypePayloadCache,
    staged_encoding: Option<R0ProgramEncoding>,
    device_capacity: R0PrototypeDeviceCapacity,
}

impl R0PrototypeHarness {
    pub fn new_correctness(
        coordinate: &FrozenR0Coordinate,
        input: &ResolvedR0Input,
    ) -> Result<Self, R0PrototypeHarnessError> {
        let mut payloads = R0PrototypePayloadCache::build(coordinate, input)?;
        let base = R0Harness::new(coordinate, input)
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))?;
        let device_capacity = R0PrototypeDeviceCapacity::query()?;
        payloads
            .bind_runtime(base.prototype_descriptor_seed())
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))?;
        Ok(Self {
            base,
            payloads,
            staged_encoding: None,
            device_capacity,
        })
    }

    pub fn new_sectioned_correctness(
        coordinate: &FrozenR0Coordinate,
        input: &ResolvedR0Input,
        manifest: &R0SectionedManifestV1,
        policy: R0SectionedShapePolicy,
    ) -> Result<(Self, u16, Vec<R0SectionedSymbolV1>), R0PrototypeHarnessError> {
        // All lowering and exact generated-symbol validation is deliberately
        // complete before R0Harness performs its first CUDA allocation.
        let mut payloads = R0PrototypePayloadCache::build(coordinate, input)?;
        let (shape_bits, candidates) = payloads.resolve_sectioned_candidates(manifest, policy)?;
        let base = R0Harness::new(coordinate, input)
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))?;
        let device_capacity = R0PrototypeDeviceCapacity::query()?;
        payloads
            .bind_runtime(base.prototype_descriptor_seed())
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))?;
        Ok((
            Self {
                base,
                payloads,
                staged_encoding: None,
                device_capacity,
            },
            shape_bits,
            candidates,
        ))
    }

    pub fn new_prepared_production(
        coordinate: &FrozenR0Coordinate,
        prepared: crate::r0_input::PreparedR0ProductionInput,
        preflight: crate::r0_geometry::R0MemoryPreflight,
    ) -> Result<Self, R0PrototypeHarnessError> {
        let mut payloads = R0PrototypePayloadCache::build(coordinate, prepared.resolved())?;
        let base = R0Harness::new_prepared_production(coordinate, prepared, preflight)
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))?;
        let device_capacity = R0PrototypeDeviceCapacity::query()?;
        payloads
            .bind_runtime(base.prototype_descriptor_seed())
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))?;
        Ok(Self {
            base,
            payloads,
            staged_encoding: None,
            device_capacity,
        })
    }

    pub fn new_prepared_sectioned_production(
        coordinate: &FrozenR0Coordinate,
        prepared: crate::r0_input::PreparedR0ProductionInput,
        preflight: crate::r0_geometry::R0MemoryPreflight,
        manifest: &R0SectionedManifestV1,
    ) -> Result<(Self, u16, Vec<R0SectionedSymbolV1>), R0PrototypeHarnessError> {
        Self::new_prepared_sectioned_production_for_policy(
            coordinate,
            prepared,
            preflight,
            manifest,
            R0SectionedShapePolicy::Exact,
        )
    }

    pub fn new_prepared_sectioned_production_for_policy(
        coordinate: &FrozenR0Coordinate,
        prepared: crate::r0_input::PreparedR0ProductionInput,
        preflight: crate::r0_geometry::R0MemoryPreflight,
        manifest: &R0SectionedManifestV1,
        policy: R0SectionedShapePolicy,
    ) -> Result<(Self, u16, Vec<R0SectionedSymbolV1>), R0PrototypeHarnessError> {
        // Resolve and validate the exact lowered shape before the first CUDA
        // allocation, preserving the correctness constructor's fail-closed
        // binding boundary for production-sized inputs.
        let mut payloads = R0PrototypePayloadCache::build(coordinate, prepared.resolved())?;
        let (shape_bits, candidates) = payloads.resolve_sectioned_candidates(manifest, policy)?;
        let base = R0Harness::new_prepared_production(coordinate, prepared, preflight)
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))?;
        let device_capacity = R0PrototypeDeviceCapacity::query()?;
        payloads
            .bind_runtime(base.prototype_descriptor_seed())
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))?;
        Ok((
            Self {
                base,
                payloads,
                staged_encoding: None,
                device_capacity,
            },
            shape_bits,
            candidates,
        ))
    }

    pub fn manifest() -> Result<R0PrototypeManifestV1, R0PrototypeHarnessError> {
        build_r0_prototype_manifest().map_err(|error| R0PrototypeHarnessError(error.to_string()))
    }

    pub fn base(&self) -> &R0Harness {
        &self.base
    }

    pub const fn device_capacity(&self) -> R0PrototypeDeviceCapacity {
        self.device_capacity
    }

    pub fn launchability(
        &self,
        config: &R0PrototypeRunConfig,
    ) -> Result<R0PrototypeLaunchability, R0PrototypeHarnessError> {
        let descriptor = Self::descriptor_for(&self.payloads, config)?;
        Ok(self
            .device_capacity
            .classify(descriptor.max_dynamic_shared_bytes()))
    }

    pub fn descriptor(
        &self,
        config: &R0PrototypeRunConfig,
    ) -> Result<&PreparedPrototypeDescriptor, R0PrototypeHarnessError> {
        Self::descriptor_for(&self.payloads, config)
    }

    pub fn sectioned_descriptor(&self) -> &PreparedPrototypeDescriptor {
        &self.payloads.dedicated_sectioned
    }

    fn descriptor_for<'a>(
        payloads: &'a R0PrototypePayloadCache,
        config: &R0PrototypeRunConfig,
    ) -> Result<&'a PreparedPrototypeDescriptor, R0PrototypeHarnessError> {
        if config.measurement.configuration_id == DEDICATED_GROUPED_CONTROL_ID {
            return Ok(&payloads.dedicated_grouped);
        }
        let capacity = match config.measurement.tile_capacity {
            None => None,
            Some(8) => Some(R0TileCapacity::C8),
            Some(16) => Some(R0TileCapacity::C16),
            Some(32) => Some(R0TileCapacity::C32),
            Some(capacity) => {
                return Err(R0PrototypeHarnessError(format!(
                    "unsupported prototype tile capacity {capacity}"
                )));
            }
        };
        payloads
            .descriptor(config.candidate.encoding, capacity)
            .ok_or_else(|| {
                R0PrototypeHarnessError(format!(
                    "missing descriptor for {}",
                    config.measurement.configuration_id
                ))
            })
    }

    fn stage_encoding(
        base: &mut R0Harness,
        payloads: &R0PrototypePayloadCache,
        staged_encoding: &mut Option<R0ProgramEncoding>,
        encoding: R0ProgramEncoding,
    ) -> Result<(), R0PrototypeHarnessError> {
        if *staged_encoding == Some(encoding) {
            return Ok(());
        }
        let coefficients = payloads.coefficient_bank(encoding).ok_or_else(|| {
            R0PrototypeHarnessError(format!(
                "missing coefficient bank for {}",
                encoding.as_str()
            ))
        })?;
        base.stage_prototype_coefficients(coefficients)
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))?;
        *staged_encoding = Some(encoding);
        Ok(())
    }

    pub fn run_configuration(
        &mut self,
        config: &R0PrototypeRunConfig,
    ) -> Result<R0Observed, R0PrototypeHarnessError> {
        let Self {
            base,
            payloads,
            staged_encoding,
            device_capacity,
        } = self;
        Self::stage_encoding(base, payloads, staged_encoding, config.candidate.encoding)?;
        let descriptor = Self::descriptor_for(payloads, config)?;
        let dynamic_shared_bytes = descriptor.max_dynamic_shared_bytes();
        let launchability = device_capacity.classify(dynamic_shared_bytes);
        if let R0PrototypeLaunchability::UnlaunchableCapacity {
            required_bytes,
            device_limit_bytes,
        } = launchability
        {
            return Err(R0PrototypeHarnessError(format!(
                "unlaunchable prototype capacity: required={required_bytes} limit={device_limit_bytes}"
            )));
        }
        if config.candidate.source_policy == R0SourcePolicy::Materialized
            && matches!(
                launchability,
                R0PrototypeLaunchability::Launchable { opt_in: true, .. }
            )
        {
            configure_materialized_shared_memory(&config.candidate, dynamic_shared_bytes).map_err(
                |error| {
                    R0PrototypeHarnessError(format!(
                        "configure materialized shared memory: {error:?}"
                    ))
                },
            )?;
        }
        let candidate = &config.candidate;
        base.run_specialized_once(candidate.geometry, |stream, plan| {
            launch_r0_prototype(candidate, descriptor, plan, dynamic_shared_bytes, stream)
        })
        .map_err(|error| R0PrototypeHarnessError(error.to_string()))
    }

    pub fn run_sectioned_candidate(
        &mut self,
        candidate: &R0SectionedSymbolV1,
    ) -> Result<R0Observed, R0PrototypeHarnessError> {
        self.base
            .stage_prototype_coefficients(&self.payloads.dedicated_sectioned_bank)
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))?;
        // A later generic grouped-slot launch must not reuse the sectioned
        // coefficient bank merely because both encodings share a descriptor.
        self.staged_encoding = None;
        let descriptor = &self.payloads.dedicated_sectioned;
        self.base
            .run_specialized_once(
                r0_sectioned_base_geometry(candidate.geometry),
                |stream, plan| launch_r0_sectioned(candidate, descriptor, plan, stream),
            )
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))
    }

    pub fn measure_configuration(
        &mut self,
        config: &R0PrototypeRunConfig,
        timing: R0TimingConfig,
    ) -> Result<R0TimedSession, R0PrototypeHarnessError> {
        let Self {
            base,
            payloads,
            staged_encoding,
            device_capacity,
        } = self;
        Self::stage_encoding(base, payloads, staged_encoding, config.candidate.encoding)?;
        let descriptor = Self::descriptor_for(payloads, config)?;
        let dynamic_shared_bytes = descriptor.max_dynamic_shared_bytes();
        let launchability = device_capacity.classify(dynamic_shared_bytes);
        if let R0PrototypeLaunchability::UnlaunchableCapacity {
            required_bytes,
            device_limit_bytes,
        } = launchability
        {
            return Err(R0PrototypeHarnessError(format!(
                "unlaunchable prototype capacity: required={required_bytes} limit={device_limit_bytes}"
            )));
        }
        if config.candidate.source_policy == R0SourcePolicy::Materialized
            && matches!(
                launchability,
                R0PrototypeLaunchability::Launchable { opt_in: true, .. }
            )
        {
            configure_materialized_shared_memory(&config.candidate, dynamic_shared_bytes).map_err(
                |error| {
                    R0PrototypeHarnessError(format!(
                        "configure materialized shared memory: {error:?}"
                    ))
                },
            )?;
        }
        let candidate = &config.candidate;
        base.measure_specialized(candidate.geometry, timing, |stream, plan| {
            launch_r0_prototype(candidate, descriptor, plan, dynamic_shared_bytes, stream)
        })
        .map_err(|error| R0PrototypeHarnessError(error.to_string()))
    }

    pub fn measure_sectioned_candidate(
        &mut self,
        candidate: &R0SectionedSymbolV1,
        timing: R0TimingConfig,
    ) -> Result<R0TimedSession, R0PrototypeHarnessError> {
        self.base
            .stage_prototype_coefficients(&self.payloads.dedicated_sectioned_bank)
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))?;
        self.staged_encoding = None;
        let descriptor = &self.payloads.dedicated_sectioned;
        self.base
            .measure_specialized(
                r0_sectioned_base_geometry(candidate.geometry),
                timing,
                |stream, plan| launch_r0_sectioned(candidate, descriptor, plan, stream),
            )
            .map_err(|error| R0PrototypeHarnessError(error.to_string()))
    }
}

impl R0PrototypePayloadCache {
    pub fn build(
        coordinate: &FrozenR0Coordinate,
        input: &ResolvedR0Input,
    ) -> Result<Self, R0PrototypeHarnessError> {
        if input.identity.circuit != coordinate.circuit || input.identity.layer != coordinate.layer
        {
            return Err(R0PrototypeHarnessError(format!(
                "prototype input coordinate mismatch: expected {}:{}, observed {}:{}",
                coordinate.circuit, coordinate.layer, input.identity.circuit, input.identity.layer
            )));
        }
        let context = program_bank()?
            .get(&(coordinate.circuit.clone(), coordinate.layer))
            .ok_or_else(|| {
                R0PrototypeHarnessError(format!(
                    "missing prototype programs for {}:{}",
                    coordinate.circuit, coordinate.layer
                ))
            })?;
        let descriptors =
            build_prototype_descriptors(coordinate, &context.programs, input.identity.log_trace)
                .map_err(|error| {
                    R0PrototypeHarnessError(format!("prototype descriptors: {error:?}"))
                })?;
        let dedicated_grouped = Box::new(
            build_dedicated_grouped_descriptor(
                coordinate,
                &context.programs,
                input.identity.log_trace,
            )
            .map_err(|error| {
                R0PrototypeHarnessError(format!("dedicated grouped descriptor: {error:?}"))
            })?,
        );
        let dedicated_sectioned = Box::new(
            build_dedicated_sectioned_descriptor(
                coordinate,
                &context.programs,
                input.identity.log_trace,
            )
            .map_err(|error| {
                R0PrototypeHarnessError(format!("dedicated sectioned descriptor: {error:?}"))
            })?,
        );
        let dedicated_sectioned_bank = resolve_dedicated_coefficient_plans(
            &dedicated_sectioned.dedicated_coefficient_plans,
            &input.identity.challenge_bases,
        )?;
        if dedicated_sectioned_bank.len() > R0_COEFFICIENT_CAPACITY {
            return Err(R0PrototypeHarnessError(format!(
                "dedicated sectioned coefficient capacity exceeded: {} > {}",
                dedicated_sectioned_bank.len(),
                R0_COEFFICIENT_CAPACITY
            )));
        }

        let mut coefficient_banks = BTreeMap::new();
        for descriptor in descriptors.iter().filter(|row| row.capacity.is_none()) {
            let bank = resolve_r0_coefficients(
                &descriptor.coefficient_recipes,
                &input.identity.challenge_bases,
            )
            .map_err(|error| {
                R0PrototypeHarnessError(format!("prototype coefficients: {error:?}"))
            })?;
            if bank.len() > R0_COEFFICIENT_CAPACITY {
                return Err(R0PrototypeHarnessError(format!(
                    "prototype coefficient capacity exceeded for {}: {} > {}",
                    descriptor.encoding.as_str(),
                    bank.len(),
                    R0_COEFFICIENT_CAPACITY
                )));
            }
            coefficient_banks.insert(descriptor.encoding, bank);
        }

        if descriptors
            .iter()
            .any(|descriptor| coefficient_banks.get(&descriptor.encoding).is_none())
        {
            return Err(R0PrototypeHarnessError(
                "prototype descriptor lacks coefficient bank".to_owned(),
            ));
        }

        Ok(Self {
            descriptors,
            dedicated_grouped,
            dedicated_sectioned,
            coefficient_banks,
            dedicated_sectioned_bank,
        })
    }

    pub fn len(&self) -> usize {
        self.descriptors.len()
    }

    pub fn is_empty(&self) -> bool {
        self.descriptors.is_empty()
    }

    pub fn ordinary_count(&self) -> usize {
        self.descriptors
            .iter()
            .filter(|descriptor| descriptor.capacity.is_none())
            .count()
    }

    pub fn materialized_count(&self) -> usize {
        self.descriptors
            .iter()
            .filter(|descriptor| descriptor.capacity.is_some())
            .count()
    }

    pub fn descriptor(
        &self,
        encoding: R0ProgramEncoding,
        capacity: Option<R0TileCapacity>,
    ) -> Option<&PreparedPrototypeDescriptor> {
        self.descriptors
            .iter()
            .find(|descriptor| descriptor.encoding == encoding && descriptor.capacity == capacity)
    }

    pub fn descriptor_by_capacity(
        &self,
        encoding: R0ProgramEncoding,
        capacity: u8,
    ) -> Option<&PreparedPrototypeDescriptor> {
        self.descriptors.iter().find(|descriptor| {
            descriptor.encoding == encoding
                && descriptor
                    .capacity
                    .is_some_and(|value| value.identities() == usize::from(capacity))
        })
    }

    pub fn coefficient_bank(&self, encoding: R0ProgramEncoding) -> Option<&[E4]> {
        self.coefficient_banks.get(&encoding).map(Vec::as_slice)
    }

    pub fn dedicated_sectioned_descriptor(&self) -> &PreparedPrototypeDescriptor {
        &self.dedicated_sectioned
    }

    pub fn dedicated_sectioned_coefficient_bank(&self) -> &[E4] {
        &self.dedicated_sectioned_bank
    }

    pub fn resolve_sectioned_candidates(
        &self,
        manifest: &R0SectionedManifestV1,
        policy: R0SectionedShapePolicy,
    ) -> Result<(u16, Vec<R0SectionedSymbolV1>), R0PrototypeHarnessError> {
        let R0PrototypePayload::GroupedSlotOrdinary(desc) = &self.dedicated_sectioned.payload
        else {
            return Err(R0PrototypeHarnessError(
                "dedicated sectioned descriptor has the wrong payload".to_owned(),
            ));
        };
        let shape_bits = u16::try_from(desc.meta.sections[4]).map_err(|_| {
            R0PrototypeHarnessError("dedicated sectioned shape does not fit u16".to_owned())
        })?;
        let requested_shapes = match policy {
            R0SectionedShapePolicy::Exact => vec![Some(
                resolve_r0_sectioned_compiled_shape(manifest, shape_bits)
                    .map_err(|error| R0PrototypeHarnessError(error.to_string()))?,
            )],
            R0SectionedShapePolicy::Compatible => {
                r0_sectioned_compatible_compiled_shapes(manifest, shape_bits)
                    .map_err(|error| R0PrototypeHarnessError(error.to_string()))?
                    .into_iter()
                    .map(Some)
                    .collect()
            }
            R0SectionedShapePolicy::Universal => vec![None],
        };
        let candidates = manifest
            .symbols
            .iter()
            .filter(|candidate| requested_shapes.contains(&candidate.shape_bits))
            .cloned()
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return Err(R0PrototypeHarnessError(format!(
                "sectioned manifest has no candidates for compiled shapes {requested_shapes:?}"
            )));
        }
        Ok((shape_bits, candidates))
    }

    pub fn canonical_expected(
        coordinate: &FrozenR0Coordinate,
        input: &ResolvedR0Input,
    ) -> Result<[crate::r0_input::FrozenE4; 27], R0PrototypeHarnessError> {
        let context = program_bank()?
            .get(&(coordinate.circuit.clone(), coordinate.layer))
            .ok_or_else(|| {
                R0PrototypeHarnessError(format!(
                    "missing canonical layer for {}:{}",
                    coordinate.circuit, coordinate.layer
                ))
            })?;
        let cells = crate::r0_reference::evaluate_canonical_r0_convention(
            &context.canonical,
            &coordinate.binding,
            input,
        )
        .map_err(|error| R0PrototypeHarnessError(format!("canonical R0 reference: {error:?}")))?;
        Ok(core::array::from_fn(|index| {
            crate::r0_input::FrozenE4::from_e4(cells[index])
        }))
    }

    pub(crate) fn bind_runtime(
        &mut self,
        seed: crate::r0_abi::R0VmDesc,
    ) -> Result<(), R0PrototypeHarnessError> {
        for descriptor in &mut self.descriptors {
            descriptor.bind_runtime(seed).map_err(|error| {
                R0PrototypeHarnessError(format!("bind prototype runtime: {error:?}"))
            })?;
        }
        self.dedicated_grouped.bind_runtime(seed).map_err(|error| {
            R0PrototypeHarnessError(format!("bind dedicated grouped runtime: {error:?}"))
        })?;
        self.dedicated_sectioned
            .bind_runtime(seed)
            .map_err(|error| {
                R0PrototypeHarnessError(format!("bind dedicated sectioned runtime: {error:?}"))
            })?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::r0_abi::R0WindowAddr;
    use crate::r0_artifact::{decode_r0_bundle, R0_CORPUS_BYTES};
    use crate::r0_input::build_prepared_r0_production_input;
    use crate::r0_prototype_manifest::{R0ProgramEncoding, R0SectionedGeometry};

    use super::{R0PrototypeDeviceCapacity, R0PrototypeLaunchability, R0PrototypePayloadCache};

    #[test]
    fn cpu_materialized_launchability_distinguishes_default_optin_and_unlaunchable() {
        let capacity = R0PrototypeDeviceCapacity {
            default_shared_bytes: 48 * 1024,
            opt_in_shared_bytes: 100 * 1024,
        };
        assert_eq!(
            capacity.classify(0),
            R0PrototypeLaunchability::Launchable {
                dynamic_shared_bytes: 0,
                opt_in: false,
            }
        );
        assert_eq!(
            capacity.classify(32 * 1024),
            R0PrototypeLaunchability::Launchable {
                dynamic_shared_bytes: 32 * 1024,
                opt_in: false,
            }
        );
        assert_eq!(
            capacity.classify(64 * 1024),
            R0PrototypeLaunchability::Launchable {
                dynamic_shared_bytes: 64 * 1024,
                opt_in: true,
            }
        );
        assert_eq!(
            capacity.classify(128 * 1024),
            R0PrototypeLaunchability::UnlaunchableCapacity {
                required_bytes: 128 * 1024,
                device_limit_bytes: 100 * 1024,
            }
        );
    }

    #[test]
    fn cpu_payload_cache_builds_all_encodings_and_capacities_before_cuda() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = bundle
            .coordinates
            .iter()
            .find(|row| row.circuit == "add_sub_lui_auipc_mop" && row.layer == 0)
            .unwrap();
        let input = build_prepared_r0_production_input(coordinate, 3, 0).unwrap();
        let cache = R0PrototypePayloadCache::build(coordinate, input.resolved()).unwrap();

        assert_eq!(cache.ordinary_count(), 8);
        assert_eq!(cache.materialized_count(), 24);
        assert_eq!(cache.len(), 32);
        let generic_grouped = cache
            .descriptor(R0ProgramEncoding::GroupedSlot, None)
            .unwrap();
        assert_ne!(
            cache.dedicated_grouped.program_sha256,
            generic_grouped.program_sha256
        );
        assert_eq!(
            cache.dedicated_grouped.coefficient_recipes,
            generic_grouped.coefficient_recipes
        );
        for encoding in R0ProgramEncoding::ALL {
            assert!(cache.descriptor(encoding, None).is_some());
            assert!(cache.coefficient_bank(encoding).is_some());
            assert!(cache.coefficient_bank(encoding).unwrap().len() <= 80);
            for capacity in [8, 16, 32] {
                let descriptor = cache.descriptor_by_capacity(encoding, capacity).unwrap();
                assert_eq!(descriptor.capacity.unwrap().identities(), capacity as usize);
                assert!(descriptor.tile_sha256.is_some());
            }
        }
    }

    #[test]
    fn cpu_payload_cache_resolves_exact_sectioned_family_before_cuda() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = bundle
            .coordinates
            .iter()
            .find(|row| row.circuit == "add_sub_lui_auipc_mop" && row.layer == 0)
            .unwrap();
        let input = build_prepared_r0_production_input(coordinate, 3, 0).unwrap();
        let cache = R0PrototypePayloadCache::build(coordinate, input.resolved()).unwrap();
        let manifest = crate::r0_prototype_manifest::build_r0_sectioned_manifest_v4().unwrap();
        let (shape_bits, candidates) = cache
            .resolve_sectioned_candidates(
                &manifest,
                crate::r0_prototype_kernels::R0SectionedShapePolicy::Exact,
            )
            .unwrap();
        assert_eq!(candidates.len(), 2);
        assert!(candidates
            .iter()
            .all(|candidate| candidate.shape_bits == Some(shape_bits)));
        assert_eq!(
            candidates
                .iter()
                .map(|candidate| (candidate.geometry, candidate.min_blocks))
                .collect::<Vec<_>>(),
            vec![
                (R0SectionedGeometry::Wide9, Some(3)),
                (R0SectionedGeometry::Wide9, Some(4)),
            ],
        );

        let (_, universal) = cache
            .resolve_sectioned_candidates(
                &manifest,
                crate::r0_prototype_kernels::R0SectionedShapePolicy::Universal,
            )
            .unwrap();
        assert_eq!(universal.len(), 2);
        assert!(universal
            .iter()
            .all(|candidate| candidate.shape_bits.is_none()));
        assert!(candidates
            .iter()
            .chain(universal.iter())
            .all(|candidate| candidate.geometry
                != crate::r0_prototype_manifest::R0SectionedGeometry::Serial3High));

        let mut tampered = manifest;
        let selected_id = candidates[0].candidate_id.clone();
        let selected = tampered
            .symbols
            .iter_mut()
            .find(|row| row.candidate_id == selected_id)
            .unwrap();
        selected.symbol.push_str("_tampered");
        let error = cache
            .resolve_sectioned_candidates(
                &tampered,
                crate::r0_prototype_kernels::R0SectionedShapePolicy::Exact,
            )
            .unwrap_err()
            .to_string();
        assert!(error.contains("schema-v4 row mismatch"), "{error}");
    }

    #[test]
    fn cpu_payload_cache_resolves_retained_alias_and_restored_identity_before_cuda() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let manifest = crate::r0_prototype_manifest::build_r0_sectioned_manifest_v4().unwrap();
        for (circuit, lowered, compiled) in [
            ("bigint_with_extended_control", 0x9bf, 0xbff),
            ("unsigned_mul_div", 0x3fb, 0x3fb),
        ] {
            let coordinate = bundle
                .coordinates
                .iter()
                .find(|row| row.circuit == circuit && row.layer == 0)
                .unwrap();
            let input = build_prepared_r0_production_input(coordinate, 3, 0).unwrap();
            let cache = R0PrototypePayloadCache::build(coordinate, input.resolved()).unwrap();
            let (lowered_shape_bits, candidates) = cache
                .resolve_sectioned_candidates(
                    &manifest,
                    crate::r0_prototype_kernels::R0SectionedShapePolicy::Exact,
                )
                .unwrap();
            assert_eq!(lowered_shape_bits, lowered);
            assert_eq!(candidates.len(), 2);
            assert!(candidates.iter().all(|candidate| {
                candidate.shape_bits == Some(compiled)
                    && candidate.geometry == R0SectionedGeometry::Wide9
                    && [Some(3), Some(4)].contains(&candidate.min_blocks)
            }));
        }
    }

    #[test]
    fn cpu_payload_cache_resolves_every_compatible_union_shape_before_cuda() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = bundle
            .coordinates
            .iter()
            .find(|row| row.circuit == "unsigned_mul_div" && row.layer == 0)
            .unwrap();
        let input = build_prepared_r0_production_input(coordinate, 3, 0).unwrap();
        let cache = R0PrototypePayloadCache::build(coordinate, input.resolved()).unwrap();
        let manifest =
            crate::r0_prototype_manifest::build_r0_sectioned_manifest_v4_for_merge_policy(
                crate::r0_prototype_manifest::R0SectionedShapeMergePolicy::UnionBank,
            )
            .unwrap();
        let (lowered, candidates) = cache
            .resolve_sectioned_candidates(
                &manifest,
                crate::r0_prototype_kernels::R0SectionedShapePolicy::Compatible,
            )
            .unwrap();
        assert_eq!(lowered, 0x3fb);
        assert_eq!(candidates.len(), 16);
        assert_eq!(
            candidates
                .iter()
                .filter_map(|candidate| candidate.shape_bits)
                .collect::<std::collections::BTreeSet<_>>(),
            [0x3fb, 0x3ff, 0x7fb, 0x7ff, 0xbfb, 0xbff, 0xffb, 0xfff]
                .into_iter()
                .collect(),
        );
        assert!(candidates.iter().all(|candidate| candidate
            .shape_bits
            .is_some_and(|shape| lowered & !shape == 0)));
    }

    #[test]
    fn cpu_runtime_binding_updates_all_payloads_without_reencoding() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = bundle
            .coordinates
            .iter()
            .find(|row| row.circuit == "add_sub_lui_auipc_mop" && row.layer == 0)
            .unwrap();
        let input = build_prepared_r0_production_input(coordinate, 3, 0).unwrap();
        let mut cache = R0PrototypePayloadCache::build(coordinate, input.resolved()).unwrap();
        let hashes = cache
            .descriptors
            .iter()
            .map(|descriptor| descriptor.program_sha256.clone())
            .collect::<Vec<_>>();
        let mut seed = match &cache
            .descriptor(R0ProgramEncoding::CurrentFixedSlot, None)
            .unwrap()
            .payload
        {
            crate::r0_prototype_abi::R0PrototypePayload::CurrentOrdinary(desc) => *desc,
            _ => unreachable!(),
        };
        seed.eq_low = core::ptr::dangling();
        seed.partials = core::ptr::dangling_mut();

        cache.bind_runtime(seed).unwrap();

        for descriptor in &cache.descriptors {
            let common = descriptor.runtime_common();
            assert_eq!(common.window_bases, seed.window_bases);
            assert_eq!(common.eq_low, seed.eq_low);
            assert_eq!(common.partials, seed.partials);
            assert_eq!(common.log_rows, seed.log_rows);
        }
        let dedicated_common = cache.dedicated_grouped.runtime_common();
        let bound_windows = coordinate.binding.windows.len();
        assert_eq!(
            dedicated_common.window_bases[..bound_windows],
            seed.window_bases[..bound_windows]
        );
        assert!(dedicated_common.window_bases[bound_windows..]
            .iter()
            .all(R0WindowAddr::is_zero));
        assert_eq!(dedicated_common.eq_low, seed.eq_low);
        assert_eq!(dedicated_common.partials, seed.partials);
        assert_eq!(dedicated_common.log_rows, seed.log_rows);
        assert_eq!(
            cache
                .descriptors
                .iter()
                .map(|descriptor| descriptor.program_sha256.clone())
                .collect::<Vec<_>>(),
            hashes
        );
    }

    #[test]
    fn cpu_current_materialized_record_locals_match_wire_classes() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = bundle
            .coordinates
            .iter()
            .find(|row| row.circuit == "add_sub_lui_auipc_mop" && row.layer == 0)
            .unwrap();
        let input = build_prepared_r0_production_input(coordinate, 3, 0).unwrap();
        let cache = R0PrototypePayloadCache::build(coordinate, input.resolved()).unwrap();
        let descriptor = cache
            .descriptor_by_capacity(R0ProgramEncoding::CurrentFixedSlot, 8)
            .unwrap();
        let crate::r0_prototype_abi::R0PrototypePayload::CurrentMaterialized(desc) =
            &descriptor.payload
        else {
            unreachable!();
        };
        for tile in &desc.tiles[..desc.tile_meta.tile_count as usize] {
            let bf_count = (tile.source_counts & 0xff) as u8;
            for record in
                usize::from(tile.first_record)..usize::from(tile.first_record + tile.record_count)
            {
                let class = (desc.ordinary.program[4 * record] >> 13) as u8;
                let local = desc.record_local_sources[record];
                let is_bf = |source: u8| source < bf_count;
                match class {
                    0 => assert!(is_bf(local[0]), "record {record} class0 {local:?}"),
                    1 => assert!(!is_bf(local[0]), "record {record} class1 {local:?}"),
                    2 => assert!(
                        is_bf(local[0]) && is_bf(local[1]),
                        "record {record} class2 {local:?}"
                    ),
                    3 => assert!(
                        is_bf(local[0]) && !is_bf(local[1]),
                        "record {record} class3 {local:?}"
                    ),
                    4 => assert!(
                        !is_bf(local[0]) && !is_bf(local[1]),
                        "record {record} class4 {local:?}"
                    ),
                    _ => panic!("invalid class {class}"),
                }
            }
        }
    }

    #[test]
    fn cpu_payload_cache_builds_every_corpus_coordinate_with_the_abi_coefficient_capacity() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        for coordinate in &bundle.coordinates {
            let input = build_prepared_r0_production_input(coordinate, 3, 0).unwrap();
            let cache = R0PrototypePayloadCache::build(coordinate, input.resolved()).unwrap();
            assert_eq!(
                cache.descriptors.len(),
                32,
                "{}:{}",
                coordinate.circuit,
                coordinate.layer
            );
        }
    }
}
