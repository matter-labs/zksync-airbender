#include <algorithm>
#include <array>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <variant>
#include <vector>

#if defined(AIRBENDER_STL_ENFORCE_FLAGS)
#if __STDC_HOSTED__ != 1
#error "STL profile requires hosted libstdc++ headers."
#endif

#if defined(__EXCEPTIONS)
#error "STL profile expects -fno-exceptions."
#endif

#if defined(__GXX_RTTI)
#error "STL profile expects -fno-rtti."
#endif
#endif

namespace {

// Keep this translation unit as a compile-time contract for the starter
// profile: these headers and core operations must stay available.
[[maybe_unused]] int stl_compile_probe() {
    std::array<int, 3> fixed = {1, 2, 3};
    std::vector<int> dynamic(fixed.begin(), fixed.end());
    std::map<int, int> ordered = {{1, 10}, {2, 20}};
    std::unordered_map<int, int> hashed = {{3, 30}, {4, 40}};

    std::string text = "airbender";
    std::string_view view = text;
    std::optional<int> maybe = 7;
    std::variant<int, long> tagged = 9L;
    std::tuple<int, int> pair = {ordered[1], hashed[3]};

    int sum = std::accumulate(dynamic.begin(), dynamic.end(), 0);
    std::sort(dynamic.begin(), dynamic.end());

    auto ptr = std::make_unique<int>(std::get<0>(pair));
    int payload = maybe.value_or(0) + static_cast<int>(view.size());
    payload += std::visit([](auto value) { return static_cast<int>(value); }, tagged);
    return sum + *ptr + payload;
}

} // namespace
