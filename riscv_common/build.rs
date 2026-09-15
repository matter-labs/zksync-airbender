fn main() {
    #[cfg(all(
        feature = "boot_sequence",
        not(any(feature = "ram_32mb_no_heap", feature = "ram_1gb", feature = "ram_4gb"))
    ))]
    {
        panic!("At least one of the RAM size features must be enabled when compiling guest program")
    }

    #[cfg(feature = "boot_sequence")]
    {
        let path = cfg_select! {
            feature = "ram_32mb_no_heap" => "32mb_total_no_heap",
            feature = "ram_1gb" => "1gb_total",
            feature = "ram_4gb" => "4gb_total",
        };
        use std::env;
        use std::fs;
        use std::path::PathBuf;
        let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
        fs::copy(&format!("src/lds/{}/link.x", path), out_dir.join("link.x")).unwrap();
        fs::copy(
            &format!("src/lds/{}/memory.x", path),
            out_dir.join("memory.x"),
        )
        .unwrap();
        println!("cargo::rustc-link-search={}", out_dir.display());
    }
}
