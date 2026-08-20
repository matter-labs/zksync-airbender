fn main() {
    const MODE_ENV: &str = "GPU_GKR_WINDOWED_R0_PROTOTYPE_NATIVE";
    println!("cargo:rerun-if-env-changed={MODE_ENV}");
    println!("cargo:rustc-check-cfg=cfg(r0_prototype_bank_full)");
    let prototype_mode = std::env::var(MODE_ENV).unwrap_or_else(|_| "off".to_owned());
    let prototype_feature = std::env::var_os("CARGO_FEATURE_R0_PROTOTYPE_BANK").is_some();
    if prototype_feature {
        println!("cargo:rerun-if-env-changed=CUDACXX");
        let nvcc = std::env::var_os("CUDACXX").unwrap_or_else(|| "nvcc".into());
        let output = std::process::Command::new(&nvcc)
            .arg("--version")
            .output()
            .unwrap_or_else(|error| panic!("run {:?} --version: {error}", nvcc));
        assert!(output.status.success(), "nvcc --version must succeed");
        let version_text = String::from_utf8(output.stdout).expect("nvcc version must be UTF-8");
        let release = version_text
            .lines()
            .find_map(|line| line.split_once("release ").map(|(_, suffix)| suffix))
            .and_then(|suffix| suffix.split(',').next())
            .map(str::trim)
            .filter(|value| !value.is_empty())
            .unwrap_or_else(|| panic!("nvcc --version lacks a release field: {version_text}"));
        println!("cargo:rustc-env=GPU_GKR_CUDA_TOOLKIT_VERSION={release}");
    }
    if !matches!(prototype_mode.as_str(), "off" | "canary" | "full") {
        panic!("{MODE_ENV} must be exactly off, canary, or full");
    }
    assert!(
        prototype_mode == "off" || prototype_feature,
        "prototype native mode requires the r0-prototype-bank feature"
    );
    if prototype_mode == "full" {
        println!("cargo:rerun-if-env-changed=CUDAARCHS");
        let architecture = std::env::var("CUDAARCHS")
            .unwrap_or_else(|_| panic!("CUDAARCHS must be literal 120 in prototype full mode"));
        assert_eq!(
            architecture, "120",
            "CUDAARCHS must be literal 120 in prototype full mode"
        );
        println!("cargo:rustc-cfg=r0_prototype_bank_full");
    }
    let native_headers =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../core/native_headers");
    let mut archive = gpu_native_build::CudaArchive::new(
        "gpu_gkr_windowed_bench_native",
        "GPU_GKR_WINDOWED_BENCH",
    )
    .define(
        "GPU_CORE_NATIVE_INCLUDE",
        native_headers
            .to_str()
            .expect("gpu_core native header path must be valid UTF-8"),
    );
    archive = archive.define(MODE_ENV, &prototype_mode);
    archive = archive.define(
        "GPU_GKR_WINDOWED_R0_PROTOTYPE_FEATURE",
        if prototype_feature { "ON" } else { "OFF" },
    );
    for geometry in [
        "CTA288_PAIR",
        "CTA96_PARTITIONED",
        "CTA96_X0_MAJOR",
        "CTA96_X1_MAJOR",
        "CTA96_X2_MAJOR",
    ] {
        for control in ["MIN_BLOCKS", "MAXREG"] {
            let name = format!("GPU_GKR_WINDOWED_R0_{geometry}_{control}");
            println!("cargo:rerun-if-env-changed={name}");
            if let Some(value) = std::env::var_os(&name) {
                let value = value
                    .into_string()
                    .unwrap_or_else(|_| panic!("{name} must be valid UTF-8"));
                value
                    .parse::<u32>()
                    .unwrap_or_else(|_| panic!("{name} must be a nonnegative integer"));
                archive = archive.define(name, value);
            }
        }
    }
    archive.build();
}
