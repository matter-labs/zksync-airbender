namespace Sail.ArchSem

/-- Selected emulator setting: experimental extensions disabled. Source: pinned
    c_emulator/riscv_model_impl.h's default and riscv_model_impl.cpp's getter.
    This is a platform configuration binding, not an instruction definition. -/
def sys_enable_experimental_extensions (_ : Unit) : Bool := false

end Sail.ArchSem
