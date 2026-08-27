# C++ Airbender Example (riscv32im + GCC/newlib)

Basic example of compiling C/C++ code for Airbender.

## Requirements

- CMake 3.20 or newer.
- RISC-V GCC toolchain with newlib (`riscv32-unknown-elf-*` binaries).

## Building a Local Toolchain from Sources

The upstream `riscv-gnu-toolchain` build always installs into `--prefix`.
Use a workspace-local prefix to avoid any system-wide installation.

Install the prerequisites from `riscv-gnu-toolchain/README.md` first (notably
`gawk`, `bison`, `flex`, and `texinfo`).

```sh
# From the riscv-gnu-toolchain checkout
./configure \
  --prefix="$PWD/.local/rv32im-zicsr" \
  --with-arch=rv32im_zicsr \
  --with-abi=ilp32 \
  --disable-linux \
  --disable-gdb
make -j"$(nproc)" newlib
```

The toolchain binaries will be in `.local/rv32im-zicsr/bin`.

## Build

Recommended: point CMake to the local toolchain bin directory.

```sh
cmake -S . -B build \
  -DCMAKE_TOOLCHAIN_FILE=cmake/riscv32im-gcc.cmake \
  -DRISCV_GCC_BIN_DIR=<path-to-toolchain-prefix>/bin
cmake --build build
```

If the toolchain binaries are already on `PATH`, `RISCV_GCC_BIN_DIR` can be omitted.

You can also pass every required binary explicitly:

```sh
cmake -S . -B build \
  -DCMAKE_TOOLCHAIN_FILE=cmake/riscv32im-gcc.cmake \
  -DRISCV_GCC_C=<path>/riscv32-unknown-elf-gcc \
  -DRISCV_GCC_CXX=<path>/riscv32-unknown-elf-g++ \
  -DRISCV_GCC_ASM=<path>/riscv32-unknown-elf-gcc \
  -DRISCV_GCC_OBJCOPY=<path>/riscv32-unknown-elf-objcopy
cmake --build build
```

When switching toolchains, use a fresh build directory because CMake caches
compiler paths.

For release builds, add `-DCMAKE_BUILD_TYPE=Release`.

Artifacts are written to the `examples/cpp` directory:

- `app.elf`
- `app.bin`
- `app.text`

## Running

You can run the generated program with `cargo airbender`:

```sh
# From the root of the repo
cargo airbender run examples/cpp/app.bin --input examples/cpp/input.txt
```

To demonstrate strict libc-exit handling, run the sentinel input that triggers
`std::exit(0)` inside the app logic:

```sh
cargo airbender run examples/cpp/app.bin --input examples/cpp/input-exit-demo.txt
```

This sentinel run is expected to fail and print an `_exit` guidance message.

## Runtime Contract (newlib)

The syscall bridge in [`src/newlib_syscalls.cpp`](src/newlib_syscalls.cpp) follows
Airbender's explicit output model:

- Successful completion must call `airbender::finish_success(output)` with 8
  output words (`x10..x17`).
- `_exit(...)` does **not** map status `0` to success. It always reports an
  error and prints a hint over quasi-UART.
- `abort()` and failed assertions are treated as deterministic guest failures
  and terminate via `airbender::finish_error()`.
- App code can use C++ streams (`std::cout`, `std::cerr`) or C stdio
  (`printf`, `fputs`); writes are routed through the syscall bridge.
- `_write` supports only `stdout`/`stderr` through quasi-UART.
- `_read` for `stdin` is intentionally unimplemented for now, so
  `std::cin`/stdin byte reads are not part of the supported profile yet.

## STL Support

This template validates a guest-friendly subset of top-level standard library
headers in [`src/stl_probe.cpp`](src/stl_probe.cpp).

Supported subset:

- `<string>`, `<string_view>`
- `<vector>`, `<map>`, `<unordered_map>`, `<array>`
- `<tuple>`, `<optional>`, `<variant>`, `<span>`
- `<algorithm>`, `<numeric>`, `<memory>`

Not part of the guaranteed profile (even if some code compiles):

- Threading/concurrency (`<thread>`, `<mutex>`, `<future>`, ...)
- Filesystem/files (`<filesystem>`, file-backed `<fstream>` flows)
- Host environment/time/random-device dependent APIs
  (`<chrono>` clocks, `<random>` device paths, locale-heavy flows)

## Project Overview

This project contains boilerplate to compile your C/C++ code as an Airbender program.
The bootstrap entrypoint is [`_start_rust`](src/main.cpp), while application
logic lives in [`app_entrypoint`](src/app.cpp).

Other provided files:

- [app.hpp](include/app.hpp): application entrypoint contract.
- [app.cpp](src/app.cpp): app logic and output-commit flow.
- [start.S](src/start.S): startup and trap entry wiring.
- [airbender_csr.hpp](include/airbender_csr.hpp): wrappers for Airbender CSR operations.
- [quasi_uart.hpp](include/quasi_uart.hpp): low-level quasi-UART writer used by
  runtime/syscall plumbing; application code can use stdio/iostream directly.
- [newlib_syscalls.cpp](src/newlib_syscalls.cpp): newlib syscall bridge (`_write`, `_exit`, `_sbrk`, etc.).

Linker scripts used:

- [link.x](../../riscv_common/src/lds/link.x)
- [memory.x](../../riscv_common/src/lds/memory.x)

## Notes

This project is intentionally C/C++-native and does not rely on Rust guest runtime crates.
As a result, it may lag behind Rust examples when platform internals change.

## License

[MIT](../../LICENSE-MIT) or [Apache 2.0](../../LICENSE-APACHE) at your option.
