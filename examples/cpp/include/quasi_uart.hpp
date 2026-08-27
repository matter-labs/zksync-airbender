#pragma once

#include <stddef.h>
#include <stdint.h>

#include "airbender_csr.hpp"

namespace airbender {

class QuasiUART {
public:
    static constexpr uint32_t kHelloMarker = 0xFFFFFFFFu;

    constexpr QuasiUART() : buffer_{0, 0, 0, 0}, len_(0) {}

    void write_entry_sequence(size_t message_len) {
        csr_write_word(kHelloMarker);
        // Number of 32-bit words + 1 for the length word.
        size_t words = (message_len + 3) / 4;
        csr_write_word(static_cast<uint32_t>(words + 1));
        csr_write_word(static_cast<uint32_t>(message_len));
    }

    void write_word(uint32_t word) { csr_write_word(word); }

    uint32_t read_word() { return csr_read_word(); }

    void write_byte(uint8_t byte) {
        buffer_[len_] = byte;
        ++len_;
        if (len_ == 4) {
            len_ = 0;
            write_word(pack_le_u32(buffer_));
        }
    }

    void flush() {
        if (len_ == 0) {
            buffer_[0] = 0;
            buffer_[1] = 0;
            buffer_[2] = 0;
            buffer_[3] = 0;
            return;
        }
        for (size_t i = len_; i < 4; ++i) {
            buffer_[i] = 0;
        }
        len_ = 0;
        write_word(pack_le_u32(buffer_));
    }

    void write_str(const char* data, size_t len) {
        write_entry_sequence(len);
        for (size_t i = 0; i < len; ++i) {
            write_byte(static_cast<uint8_t>(data[i]));
        }
        flush();
    }

    void write_cstr(const char* s) {
        write_str(s, strlen_(s));
    }

private:
    static uint32_t pack_le_u32(const uint8_t bytes[4]) {
        return static_cast<uint32_t>(bytes[0]) |
               (static_cast<uint32_t>(bytes[1]) << 8) |
               (static_cast<uint32_t>(bytes[2]) << 16) |
               (static_cast<uint32_t>(bytes[3]) << 24);
    }

    static size_t strlen_(const char* s) {
        size_t len = 0;
        while (s[len] != '\0') {
            ++len;
        }
        return len;
    }

    uint8_t buffer_[4];
    size_t len_;
};

} // namespace airbender
