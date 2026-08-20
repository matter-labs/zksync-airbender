use serde::{Deserialize, Serialize};

use crate::r0_geometry::R0LaunchMetadata;
use crate::r0_harness::{R0TimedSample, R0TimingConfig};
use crate::r0_input::FrozenE4;
use crate::r0_prototype_harness::{R0PrototypeDeviceCapacity, R0PrototypeLaunchability};

pub const R0_PROTOTYPE_REPORT_VERSION: u32 = 2;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0PrototypeClockPolicyV2 {
    pub raw_query: String,
    pub uuid: String,
    pub name: String,
    pub compute_capability: String,
    pub driver_version: String,
    pub performance_state: String,
    pub persistence_mode: String,
    pub current_graphics_clock: String,
    pub current_memory_clock: String,
    pub max_graphics_clock: String,
    pub max_memory_clock: String,
    pub application_graphics_clock: String,
    pub application_memory_clock: String,
    pub clock_event_reasons_active: String,
}

pub fn parse_nvidia_smi_clock_policy(raw: &str) -> Result<R0PrototypeClockPolicyV2, String> {
    let lines = raw
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>();
    if lines.len() != 1 {
        return Err(format!(
            "nvidia-smi clock query must return exactly one device row, got {}",
            lines.len()
        ));
    }
    let fields = lines[0].splitn(13, ',').map(str::trim).collect::<Vec<_>>();
    if fields.len() != 13 || fields.iter().any(|field| field.is_empty()) {
        return Err(format!(
            "nvidia-smi clock query must return 13 nonempty fields, got {}",
            fields.len()
        ));
    }
    Ok(R0PrototypeClockPolicyV2 {
        raw_query: raw.to_owned(),
        uuid: fields[0].to_owned(),
        name: fields[1].to_owned(),
        compute_capability: fields[2].to_owned(),
        driver_version: fields[3].to_owned(),
        performance_state: fields[4].to_owned(),
        persistence_mode: fields[5].to_owned(),
        current_graphics_clock: fields[6].to_owned(),
        current_memory_clock: fields[7].to_owned(),
        max_graphics_clock: fields[8].to_owned(),
        max_memory_clock: fields[9].to_owned(),
        application_graphics_clock: fields[10].to_owned(),
        application_memory_clock: fields[11].to_owned(),
        clock_event_reasons_active: fields[12].to_owned(),
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0PrototypeDeviceIdentityV2 {
    pub cuda_device_index: i32,
    pub uuid: String,
    pub name: String,
    pub compute_capability_major: i32,
    pub compute_capability_minor: i32,
    pub cuda_driver_version: i32,
    pub cuda_runtime_version: i32,
    pub cuda_toolkit_version: String,
    pub default_shared_memory_bytes: usize,
    pub opt_in_shared_memory_bytes: usize,
    pub clock_policy: R0PrototypeClockPolicyV2,
}

pub fn validate_device_capacity_identity(
    identity: &R0PrototypeDeviceIdentityV2,
    capacity: R0PrototypeDeviceCapacity,
) -> Result<(), String> {
    let default_shared_memory_bytes = usize::try_from(capacity.default_shared_bytes)
        .map_err(|_| "default shared-memory capacity exceeds usize".to_owned())?;
    let opt_in_shared_memory_bytes = usize::try_from(capacity.opt_in_shared_bytes)
        .map_err(|_| "opt-in shared-memory capacity exceeds usize".to_owned())?;
    if identity.default_shared_memory_bytes != default_shared_memory_bytes
        || identity.opt_in_shared_memory_bytes != opt_in_shared_memory_bytes
        || default_shared_memory_bytes > opt_in_shared_memory_bytes
    {
        return Err(format!(
            "serialized shared-memory capacity ({}/{}) differs from launch capacity ({}/{})",
            identity.default_shared_memory_bytes,
            identity.opt_in_shared_memory_bytes,
            capacity.default_shared_bytes,
            capacity.opt_in_shared_bytes
        ));
    }
    Ok(())
}

pub fn validate_launchability_against_identity(
    identity: &R0PrototypeDeviceIdentityV2,
    launchability: R0PrototypeLaunchability,
) -> Result<(), String> {
    if identity.default_shared_memory_bytes > identity.opt_in_shared_memory_bytes {
        return Err("default shared-memory capacity exceeds opt-in capacity".to_owned());
    }
    match launchability {
        R0PrototypeLaunchability::Launchable {
            dynamic_shared_bytes,
            opt_in: false,
        } if usize::try_from(dynamic_shared_bytes).ok()
            <= Some(identity.default_shared_memory_bytes) =>
        {
            Ok(())
        }
        R0PrototypeLaunchability::Launchable {
            dynamic_shared_bytes,
            opt_in: true,
        } if usize::try_from(dynamic_shared_bytes).is_ok_and(|bytes| {
            bytes > identity.default_shared_memory_bytes
                && bytes <= identity.opt_in_shared_memory_bytes
        }) =>
        {
            Ok(())
        }
        R0PrototypeLaunchability::UnlaunchableCapacity {
            required_bytes,
            device_limit_bytes,
        } if usize::try_from(required_bytes)
            .is_ok_and(|bytes| bytes > identity.opt_in_shared_memory_bytes)
            && usize::try_from(device_limit_bytes).ok()
                == Some(identity.opt_in_shared_memory_bytes) =>
        {
            Ok(())
        }
        _ => Err("launchability contradicts serialized shared-memory capacity".to_owned()),
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0PrototypeObservationV2 {
    pub version: u32,
    pub configuration_id: String,
    pub candidate_id: String,
    pub circuit: String,
    pub layer: u32,
    pub log_trace: u32,
    pub seed: u64,
    pub input_sha256: String,
    pub program_sha256: String,
    pub tile_sha256: Option<String>,
    pub descriptor_bytes: usize,
    pub launchability: R0PrototypeLaunchability,
    pub launch: Option<R0LaunchMetadata>,
    pub cells: Option<[FrozenE4; 27]>,
    pub checksum: Option<String>,
    pub expected_checksum: Option<String>,
    pub passing: bool,
    pub failure: Option<String>,
    pub device_identity: R0PrototypeDeviceIdentityV2,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0PrototypeTimingPhaseV2 {
    Pilot,
    Retained,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct R0PrototypeTimingSampleV2 {
    pub version: u32,
    pub configuration_id: String,
    pub circuit: String,
    pub layer: u32,
    pub log_trace: u32,
    pub seed: u64,
    pub phase: R0PrototypeTimingPhaseV2,
    pub pass_index: u32,
    pub pass_position: u32,
    pub warmup: bool,
    pub sample_index: u32,
    pub milliseconds: f64,
}

impl R0PrototypeTimingSampleV2 {
    pub fn from_session(
        configuration_id: &str,
        circuit: &str,
        layer: u32,
        log_trace: u32,
        seed: u64,
        phase: R0PrototypeTimingPhaseV2,
        pass_index: u32,
        pass_position: u32,
        config: R0TimingConfig,
        samples: &[R0TimedSample],
    ) -> Result<Vec<Self>, String> {
        let expected = usize::try_from(config.warmups() + config.samples())
            .map_err(|_| "timing cardinality exceeds usize".to_owned())?;
        if samples.len() != expected {
            return Err(format!(
                "timing sample cardinality mismatch: observed={} expected={expected}",
                samples.len()
            ));
        }
        let mut measured_index = 0u32;
        let mut warmup_index = 0u32;
        samples
            .iter()
            .map(|sample| {
                if !sample.milliseconds.is_finite() || sample.milliseconds <= 0.0 {
                    return Err("prototype timing duration must be finite and positive".to_owned());
                }
                let sample_index = if sample.warmup {
                    let index = warmup_index;
                    warmup_index += 1;
                    index
                } else {
                    let index = measured_index;
                    measured_index += 1;
                    index
                };
                Ok(Self {
                    version: R0_PROTOTYPE_REPORT_VERSION,
                    configuration_id: configuration_id.to_owned(),
                    circuit: circuit.to_owned(),
                    layer,
                    log_trace,
                    seed,
                    phase: phase.clone(),
                    pass_index,
                    pass_position,
                    warmup: sample.warmup,
                    sample_index,
                    milliseconds: sample.milliseconds,
                })
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::r0_harness::{R0TimedSample, R0TimingConfig};

    use super::{
        parse_nvidia_smi_clock_policy, validate_device_capacity_identity,
        validate_launchability_against_identity, R0PrototypeClockPolicyV2,
        R0PrototypeDeviceIdentityV2, R0PrototypeTimingPhaseV2, R0PrototypeTimingSampleV2,
    };

    fn fixture_identity() -> R0PrototypeDeviceIdentityV2 {
        R0PrototypeDeviceIdentityV2 {
            cuda_device_index: 0,
            uuid: "GPU-fixture".to_owned(),
            name: "fixture".to_owned(),
            compute_capability_major: 10,
            compute_capability_minor: 0,
            cuda_driver_version: 12_090,
            cuda_runtime_version: 12_080,
            cuda_toolkit_version: "12.8".to_owned(),
            default_shared_memory_bytes: 49_152,
            opt_in_shared_memory_bytes: 232_448,
            clock_policy: R0PrototypeClockPolicyV2 {
                raw_query: "fixture\n".to_owned(),
                uuid: "GPU-fixture".to_owned(),
                name: "fixture".to_owned(),
                compute_capability: "10.0".to_owned(),
                driver_version: "fixture".to_owned(),
                performance_state: "P0".to_owned(),
                persistence_mode: "Enabled".to_owned(),
                current_graphics_clock: "1 MHz".to_owned(),
                current_memory_clock: "2 MHz".to_owned(),
                max_graphics_clock: "3 MHz".to_owned(),
                max_memory_clock: "4 MHz".to_owned(),
                application_graphics_clock: "5 MHz".to_owned(),
                application_memory_clock: "6 MHz".to_owned(),
                clock_event_reasons_active: "None".to_owned(),
            },
        }
    }

    #[test]
    fn cpu_device_capacity_identity_and_launchability_are_one_checked_fact() {
        use crate::r0_prototype_harness::{R0PrototypeDeviceCapacity, R0PrototypeLaunchability};

        let identity = fixture_identity();
        let capacity = R0PrototypeDeviceCapacity {
            default_shared_bytes: 49_152,
            opt_in_shared_bytes: 232_448,
        };
        validate_device_capacity_identity(&identity, capacity).unwrap();
        assert!(validate_device_capacity_identity(
            &identity,
            R0PrototypeDeviceCapacity {
                default_shared_bytes: 48_000,
                ..capacity
            }
        )
        .is_err());
        for launchability in [
            R0PrototypeLaunchability::Launchable {
                dynamic_shared_bytes: 49_152,
                opt_in: false,
            },
            R0PrototypeLaunchability::Launchable {
                dynamic_shared_bytes: 49_153,
                opt_in: true,
            },
            R0PrototypeLaunchability::UnlaunchableCapacity {
                required_bytes: 232_449,
                device_limit_bytes: 232_448,
            },
        ] {
            validate_launchability_against_identity(&identity, launchability).unwrap();
        }
        assert!(validate_launchability_against_identity(
            &identity,
            R0PrototypeLaunchability::Launchable {
                dynamic_shared_bytes: 49_153,
                opt_in: false,
            }
        )
        .is_err());
        assert!(validate_launchability_against_identity(
            &identity,
            R0PrototypeLaunchability::UnlaunchableCapacity {
                required_bytes: 232_449,
                device_limit_bytes: 49_152,
            }
        )
        .is_err());
    }

    #[test]
    fn cpu_clock_policy_parser_preserves_every_bound_field_and_raw_text() {
        let raw = "GPU-00112233-4455-6677-8899-aabbccddeeff, NVIDIA B200, 10.0, 590.44.01, P0, Enabled, 1837 MHz, 1593 MHz, 2100 MHz, 1600 MHz, 1800 MHz, 1500 MHz, None\n";
        let parsed = parse_nvidia_smi_clock_policy(raw).unwrap();
        assert_eq!(parsed.raw_query, raw);
        assert_eq!(parsed.uuid, "GPU-00112233-4455-6677-8899-aabbccddeeff");
        assert_eq!(parsed.compute_capability, "10.0");
        assert_eq!(parsed.persistence_mode, "Enabled");
        assert_eq!(parsed.current_graphics_clock, "1837 MHz");
        assert_eq!(parsed.application_memory_clock, "1500 MHz");
        assert_eq!(parsed.clock_event_reasons_active, "None");
    }

    #[test]
    fn cpu_clock_policy_parser_rejects_missing_or_extra_devices() {
        assert!(parse_nvidia_smi_clock_policy("").is_err());
        assert!(parse_nvidia_smi_clock_policy(
            "GPU-a, name, 10.0, driver, P0, Enabled, 1, 2, 3, 4, 5, 6, None\nGPU-b, name, 10.0, driver, P0, Enabled, 1, 2, 3, 4, 5, 6, None\n"
        )
        .is_err());
    }

    #[test]
    fn cpu_timing_rows_preserve_warmup_and_measured_indices() {
        let config = R0TimingConfig::screen(2, 3).unwrap();
        let samples = [
            R0TimedSample {
                warmup: true,
                milliseconds: 1.0,
            },
            R0TimedSample {
                warmup: true,
                milliseconds: 2.0,
            },
            R0TimedSample {
                warmup: false,
                milliseconds: 3.0,
            },
            R0TimedSample {
                warmup: false,
                milliseconds: 4.0,
            },
            R0TimedSample {
                warmup: false,
                milliseconds: 5.0,
            },
        ];
        let rows = R0PrototypeTimingSampleV2::from_session(
            "config",
            "circuit",
            0,
            20,
            0,
            R0PrototypeTimingPhaseV2::Pilot,
            0,
            7,
            config,
            &samples,
        )
        .unwrap();
        assert!(rows
            .iter()
            .all(|row| row.phase == R0PrototypeTimingPhaseV2::Pilot
                && row.pass_index == 0
                && row.pass_position == 7));
        assert_eq!(
            rows.iter().map(|row| row.sample_index).collect::<Vec<_>>(),
            vec![0, 1, 0, 1, 2]
        );
    }
}
