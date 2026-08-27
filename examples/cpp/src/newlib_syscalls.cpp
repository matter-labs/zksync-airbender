#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <sys/stat.h>

#include "airbender_csr.hpp"
#include "quasi_uart.hpp"

extern "C" {
extern uint32_t _sheap;
extern uint32_t _eheap;
}

namespace {

constexpr int kStdinFd = 0;
constexpr int kStdoutFd = 1;
constexpr int kStderrFd = 2;
constexpr intptr_t kSbrkFailure = -1;
constexpr size_t kI32BufferSize = 12;

uint8_t* g_program_break = reinterpret_cast<uint8_t*>(&_sheap);

bool is_supported_fd(int fd) {
    return fd == kStdinFd || fd == kStdoutFd || fd == kStderrFd;
}

void write_optional_field(airbender::QuasiUART& uart, const char* label, const char* value) {
    if (value == nullptr || value[0] == '\0') {
        return;
    }

    uart.write_cstr(label);
    uart.write_cstr(value);
}

void write_i32(airbender::QuasiUART& uart, int value) {
    char buffer[kI32BufferSize];
    size_t index = kI32BufferSize;
    buffer[--index] = '\0';

    bool negative = value < 0;
    unsigned magnitude = 0;
    if (negative) {
        // Convert without overflowing on INT_MIN.
        magnitude = static_cast<unsigned>(-(value + 1)) + 1U;
    } else {
        magnitude = static_cast<unsigned>(value);
    }

    do {
        buffer[--index] = static_cast<char>('0' + (magnitude % 10U));
        magnitude /= 10U;
    } while (magnitude != 0);

    if (negative) {
        buffer[--index] = '-';
    }

    uart.write_cstr(&buffer[index]);
}

[[noreturn]] void finish_error_with_message(const char* message) {
    airbender::QuasiUART uart;
    uart.write_cstr(message);
    airbender::finish_error();
}

[[noreturn]] void finish_error_for_exit_status(int status) {
    airbender::QuasiUART uart;
    uart.write_cstr("libc called _exit().");
    uart.write_cstr("Use airbender::finish_success(output) to end with success.");
    uart.write_cstr("_exit status:");
    write_i32(uart, status);
    airbender::finish_error();
}

} // namespace

extern "C" int _write(int fd, const char* buf, int len) {
    // newlib funnels stdio writes through this hook. We only surface stdout/stderr
    // via quasi-UART because that is what the guest runtime can expose today.
    if (fd != kStdoutFd && fd != kStderrFd) {
        errno = EBADF;
        return -1;
    }
    if (len < 0) {
        errno = EINVAL;
        return -1;
    }
    if (len == 0) {
        return 0;
    }
    if (buf == nullptr) {
        errno = EFAULT;
        return -1;
    }

    airbender::QuasiUART uart;
    uart.write_str(buf, static_cast<size_t>(len));
    return len;
}

extern "C" int _read(int fd, char*, int) {
    // TODO: Map fd=0 reads to Airbender's input stream when byte-oriented stdin is required.
    if (fd != kStdinFd) {
        errno = EBADF;
    } else {
        errno = ENOSYS;
    }
    return -1;
}

extern "C" int _close(int fd) {
    if (!is_supported_fd(fd)) {
        errno = EBADF;
        return -1;
    }
    return 0;
}

extern "C" int _fstat(int fd, struct stat* st) {
    if (!is_supported_fd(fd)) {
        errno = EBADF;
        return -1;
    }
    if (st == nullptr) {
        errno = EFAULT;
        return -1;
    }

    st->st_mode = S_IFCHR;
    return 0;
}

extern "C" int _isatty(int fd) {
    if (!is_supported_fd(fd)) {
        errno = EBADF;
        return 0;
    }
    return 1;
}

extern "C" int _lseek(int fd, int, int) {
    if (!is_supported_fd(fd)) {
        errno = EBADF;
        return -1;
    }

    // stdin/stdout/stderr are character devices and cannot be seeked.
    errno = ESPIPE;
    return -1;
}

extern "C" int _getpid() {
    return 1;
}

extern "C" int _kill(int, int) {
    errno = ENOSYS;
    return -1;
}

extern "C" void* _sbrk(ptrdiff_t increment) {
    // We keep a monotonic program break over the linker-defined heap range.
    // Shrinking is intentionally omitted for now because this guest does not
    // rely on returning heap pages to the runtime.
    if (increment < 0) {
        errno = ENOMEM;
        return reinterpret_cast<void*>(kSbrkFailure);
    }

    uintptr_t program_break = reinterpret_cast<uintptr_t>(g_program_break);
    uintptr_t heap_end = reinterpret_cast<uintptr_t>(&_eheap);
    size_t requested = static_cast<size_t>(increment);

    if (program_break > heap_end) {
        errno = ENOMEM;
        return reinterpret_cast<void*>(kSbrkFailure);
    }

    size_t available = static_cast<size_t>(heap_end - program_break);
    if (requested > available) {
        errno = ENOMEM;
        return reinterpret_cast<void*>(kSbrkFailure);
    }

    uintptr_t next_break = program_break + requested;
    if (next_break < program_break || next_break > heap_end) {
        errno = ENOMEM;
        return reinterpret_cast<void*>(kSbrkFailure);
    }

    void* previous_break = reinterpret_cast<void*>(program_break);
    g_program_break = reinterpret_cast<uint8_t*>(next_break);
    return previous_break;
}

extern "C" [[noreturn]] void _exit(int status) {
    // Airbender treats successful completion as an explicit output commit
    // into x10..x17, so we never map libc status codes to success.
    finish_error_for_exit_status(status);
}

extern "C" [[noreturn]] void __wrap_abort() {
    finish_error_with_message("abort() called.");
}

extern "C" [[noreturn]] void __cxa_pure_virtual() {
    finish_error_with_message("__cxa_pure_virtual() called.");
}

extern "C" [[noreturn]] void __assert_func(
    const char* file,
    int line,
    const char* function,
    const char* expression
) {
    airbender::QuasiUART uart;
    uart.write_cstr("assertion failed.");
    write_optional_field(uart, "expression:", expression);
    write_optional_field(uart, "function:", function);
    write_optional_field(uart, "file:", file);
    uart.write_cstr("line:");
    write_i32(uart, line);
    airbender::finish_error();
}

extern "C" [[noreturn]] void __assert_fail(
    const char* expression,
    const char* file,
    unsigned line,
    const char* function
) {
    // Some newlib variants route assertions through __assert_fail instead of
    // __assert_func, so keep both hooks to guarantee deterministic failures.
    __assert_func(file, static_cast<int>(line), function, expression);
}
