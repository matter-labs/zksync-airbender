cmake_minimum_required(VERSION 3.20)

project(airbender_cpp_example LANGUAGES C CXX ASM)

set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

set(LINKER_SCRIPT_DIR "${CMAKE_CURRENT_LIST_DIR}/../../riscv_common/src/lds")
set(LINKER_SCRIPT "${LINKER_SCRIPT_DIR}/link.x")
set(MEMORY_SCRIPT "${LINKER_SCRIPT_DIR}/memory.x")

add_executable(app
    src/app.cpp
    src/main.cpp
    src/newlib_syscalls.cpp
    src/stl_probe.cpp
    src/start.S
)

set_source_files_properties(
    src/stl_probe.cpp
    PROPERTIES COMPILE_DEFINITIONS AIRBENDER_STL_ENFORCE_FLAGS=1
)

target_include_directories(app PRIVATE ${CMAKE_CURRENT_LIST_DIR}/include)
target_compile_definitions(app PRIVATE AIRBENDER_USE_NEWLIB=1)

target_compile_options(app PRIVATE
    $<$<COMPILE_LANGUAGE:C>:-ffreestanding>
    -fno-exceptions
    -fno-rtti
    -fno-use-cxa-atexit
    -fno-unwind-tables
    -fno-asynchronous-unwind-tables
    -fno-stack-protector
    -fno-omit-frame-pointer
    -fdata-sections
    -ffunction-sections
)

target_link_options(app PRIVATE
    -nostartfiles
    --specs=nano.specs
    --specs=nosys.specs
    -Wl,--wrap=abort
    -Wl,-T,${MEMORY_SCRIPT}
    -Wl,-T,${LINKER_SCRIPT}
    -Wl,-e,_start
    -Wl,--gc-sections
)

set_target_properties(app PROPERTIES
    OUTPUT_NAME "app"
    SUFFIX ".elf"
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_LIST_DIR}"
)

if(NOT CMAKE_OBJCOPY)
    find_program(CMAKE_OBJCOPY NAMES riscv32-unknown-elf-objcopy llvm-objcopy objcopy)
endif()

if(CMAKE_OBJCOPY)
    add_custom_command(
        OUTPUT ${CMAKE_CURRENT_LIST_DIR}/app.bin
        # C++ iostream support pulls libstdc++ objects that contain many
        # .gcc_except_table.* sections. We compile with -fno-exceptions, so
        # these unwind tables are unused for this guest profile and only bloat
        # app.bin due linker-script orphan placement.
        COMMAND ${CMAKE_OBJCOPY} -O binary -R ".gcc_except_table" -R ".gcc_except_table.*" $<TARGET_FILE:app> ${CMAKE_CURRENT_LIST_DIR}/app.bin
        DEPENDS app
        COMMENT "Generating app.bin"
    )

    add_custom_command(
        OUTPUT ${CMAKE_CURRENT_LIST_DIR}/app.text
        COMMAND ${CMAKE_OBJCOPY} -O binary --only-section=.text $<TARGET_FILE:app> ${CMAKE_CURRENT_LIST_DIR}/app.text
        DEPENDS app
        COMMENT "Generating app.text"
    )

    add_custom_target(artifacts ALL DEPENDS ${CMAKE_CURRENT_LIST_DIR}/app.bin ${CMAKE_CURRENT_LIST_DIR}/app.text)
else()
    message(WARNING "objcopy not found; app.bin/app.text will not be generated")
endif()
