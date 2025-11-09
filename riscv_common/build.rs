fn main() {
    use std::env;
    use std::fs;
    use std::path::PathBuf;
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    fs::copy("src/lds/link.x", out_dir.join("link.x")).unwrap();
    fs::copy("src/lds/memory.x", out_dir.join("memory.x")).unwrap();
    println!("cargo::rustc-link-search={}", out_dir.display());
}
