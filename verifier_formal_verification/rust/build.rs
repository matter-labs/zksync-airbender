fn main() {
    // relink when the linker scripts or entry asm change
    println!("cargo:rerun-if-changed=lds");
    println!("cargo:rerun-if-changed=src/start.S");
}
