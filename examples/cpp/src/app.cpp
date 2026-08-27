#include "app.hpp"

#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <string>
#include <unordered_map>
#include <vector>
#include <stdint.h>

#include "airbender_csr.hpp"

namespace {

// =============================================================================
// App contract and demo mode
// =============================================================================
//
// This sample consumes one u32 input word and commits an 8-word output. For
// starter-template UX we also reserve one sentinel input that intentionally
// calls std::exit(0) to demonstrate that libc exits are treated as failures
// unless the program explicitly commits output via finish_success().
constexpr uint32_t kModulus = 7919;
constexpr uint32_t kExitDemoSentinel = 0xFFFFFFFFu;

// =============================================================================
// Pure computation routine
// =============================================================================
uint32_t fibonacci_mod(uint32_t n) {
    uint32_t a = 0;
    uint32_t b = 1;
    for (uint32_t i = 0; i < n; ++i) {
        const uint32_t c = (a + b) % kModulus;
        a = b;
        b = c;
    }
    return b;
}

// =============================================================================
// STL demo routine
// =============================================================================
//
// This routine intentionally exercises starter-template containers and string
// utilities that are expected to work in guest programs.
struct StlDemoResult {
    uint32_t checksum;
    uint32_t distinct_values;
};

StlDemoResult run_stl_demo(uint32_t n, uint32_t fib) {
    std::vector<uint32_t> samples = {
        n & 0xFFu,
        (n >> 8) & 0xFFu,
        fib & 0xFFu,
        (fib >> 8) & 0xFFu,
        n ^ fib,
    };
    std::sort(samples.begin(), samples.end());

    std::map<uint32_t, uint32_t> histogram;
    for (uint32_t value : samples) {
        ++histogram[value];
    }

    std::unordered_map<uint32_t, uint32_t> mirrored(histogram.begin(), histogram.end());
    uint32_t checksum = std::accumulate(samples.begin(), samples.end(), 0u);

    std::string message = "STL demo checksum=";
    message += std::to_string(checksum);
    message += " distinct=";
    message += std::to_string(static_cast<uint32_t>(mirrored.size()));
    std::cout << message << '\n';

    return {
        .checksum = checksum,
        .distinct_values = static_cast<uint32_t>(mirrored.size()),
    };
}

} // namespace

[[noreturn]] void app_entrypoint() {
    // Initialize iostream state explicitly from app code. Our startup path does
    // not currently rely on global C++ constructors from standard libraries.
    std::ios_base::Init iostream_runtime_init;
    (void)iostream_runtime_init;

    // =============================================================================
    // 1) Read input and log through standard streams
    // =============================================================================
    //
    // stdout/stderr are bridged by newlib_syscalls.cpp, so application code can
    // use iostream without touching quasi-UART directly.
    const uint32_t n = airbender::csr_read_word();
    std::cout << "Computing Fibonacci number with n=" << n << '\n';

    // =============================================================================
    // 2) Optional failure-contract demonstration
    // =============================================================================
    if (n == kExitDemoSentinel) {
        std::cerr << "Exit-demo sentinel observed; calling std::exit(0)." << '\n';
        // TODO: Replace this sentinel with a dedicated demo input mode once the
        // template grows a richer input format than a single u32 word.
        std::exit(0);
    }

    // =============================================================================
    // 3) Commit explicit success output for x10..x17
    // =============================================================================
    const uint32_t fib = fibonacci_mod(n);
    const StlDemoResult stl_demo = run_stl_demo(n, fib);
    std::array<uint32_t, 8> output = {fib, n, 0, 0, 0, 0, 0, 0};

    // Keep the public output contract stable for now so existing sample
    // verifiers continue to assert only fib and input words.
    (void)stl_demo;

    std::cout << "Computation finished; committing output words." << '\n';
    std::cout.flush();
    std::cerr.flush();

    airbender::finish_success(output.data());
}
