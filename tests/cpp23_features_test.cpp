// cpp23_features_test.cpp
// Comprehensive C++23 Feature Test for Transpiler Validation

#include <iostream>
#include <string>
#include <vector>
#include <array>
#include <span>
#include <ranges>
#include <algorithm>
#include <memory>
#include <optional>
#include <variant>
#include <expected>
#include <print>
#include <format>
#include <generator>
#include <coroutine>
#include <stacktrace>
#include <flat_map>
#include <flat_set>
#include <mdspan>
#include <utility>
#include <functional>
#include <tuple>
#include <type_traits>
#include <concepts>
#include <source_location>
#include <compare>
#include <spanstream>
#include <bitset>
#include <cmath>
#include <cstdint>

// ============================================================================
// 1. DEDUCING THIS (C++23)
// ============================================================================

class DeducingThisTest {
    int value_ = 42;
public:
    template<typename Self>
    auto&& getValue(this Self&& self) {
        return std::forward<Self>(self).value_;
    }
    
    template<typename Self>
    Self&& chainMethod(this Self&& self, int x) {
        self.value_ += x;
        return std::forward<Self>(self);
    }
    
    static void testRecursiveLambda() {
        auto factorial = [](this auto self, int n) -> int {
            if (n <= 1) return 1;
            return n * self(n - 1);
        };
        std::cout << "Factorial(5): " << factorial(5) << "\n";
    }
};

// ============================================================================
// 2. MULTIDIMENSIONAL SUBSCRIPT (C++23)
// ============================================================================

class Matrix {
    std::vector<std::vector<double>> data_;
public:
    Matrix(size_t rows, size_t cols) {
        data_.resize(rows, std::vector<double>(cols, 0.0));
    }
    double& operator[](size_t row, size_t col) {
        return data_[row][col];
    }
    const double& operator[](size_t row, size_t col) const {
        return data_[row][col];
    }
};

// ============================================================================
// 3. IF CONSTEVAL (C++23)
// ============================================================================

constexpr int computeValue(int x) {
    if consteval {
        return x * x;
    } else {
        return x + x;
    }
}

// ============================================================================
// 4. STATIC OPERATORS (C++23)
// ============================================================================

struct StaticCallable {
    static int operator()(int x, int y) { return x + y; }
};

struct StaticIndexable {
    static inline std::array<int, 10> data = {0,1,2,3,4,5,6,7,8,9};
    static int& operator[](size_t idx) { return data[idx]; }
};

// ============================================================================
// 5. std::expected (C++23)
// ============================================================================

std::expected<int, std::string> divide(int a, int b) {
    if (b == 0) return std::unexpected("Division by zero");
    return a / b;
}

void testExpected() {
    auto result = divide(10, 2);
    if (result) std::cout << "10 / 2 = " << *result << "\n";
    
    auto bad = divide(10, 0);
    if (!bad) std::cout << "Error: " << bad.error() << "\n";
    
    // Monadic
    auto chained = divide(100, 5)
        .and_then([](int x) { return divide(x, 2); })
        .transform([](int x) { return x * 3; });
}

// ============================================================================
// 6. std::print (C++23)
// ============================================================================

void testPrint() {
    std::print("Hello from std::print! ");
    std::println("Value: {}, String: {}", 42, "test");
}

// ============================================================================
// 7. RANGES C++23
// ============================================================================

void testRangesC23() {
    std::vector<int> nums = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
    
    // ranges::to
    auto squares = nums 
        | std::views::transform([](int x) { return x * x; })
        | std::ranges::to<std::vector>();
    
    // ranges::contains
    bool has5 = std::ranges::contains(nums, 5);
    
    // ranges::fold_left
    int sum = std::ranges::fold_left(nums, 0, std::plus{});
    
    // views::zip
    std::vector<char> chars = {'a', 'b', 'c'};
    for (auto [n, c] : std::views::zip(nums, chars)) {
        std::println("{}: {}", n, c);
    }
    
    // views::enumerate
    for (auto [idx, val] : nums | std::views::enumerate) {
        std::println("[{}] = {}", idx, val);
    }
    
    // views::chunk
    for (auto chunk : nums | std::views::chunk(3)) {
        std::print("Chunk: ");
        for (int x : chunk) std::print("{} ", x);
        std::println("");
    }
    
    // views::stride
    for (int x : nums | std::views::stride(2)) {
        std::print("{} ", x);
    }
    std::println("");
    
    // views::cartesian_product
    std::vector<int> a = {1, 2};
    std::vector<char> b = {'x', 'y'};
    for (auto [i, c] : std::views::cartesian_product(a, b)) {
        std::println("({}, {})", i, c);
    }
    
    // views::adjacent
    for (auto [x, y, z] : nums | std::views::adjacent<3>) {
        std::println("Adjacent: {}, {}, {}", x, y, z);
    }
}

// ============================================================================
// 8. std::generator (C++23)
// ============================================================================

std::generator<int> fibonacci(int n) {
    int a = 0, b = 1;
    for (int i = 0; i < n; ++i) {
        co_yield a;
        auto next = a + b;
        a = b;
        b = next;
    }
}

std::generator<int> tree_traversal(int value, int depth) {
    if (depth <= 0) co_return;
    co_yield value;
    co_yield std::ranges::elements_of(tree_traversal(value * 2, depth - 1));
    co_yield std::ranges::elements_of(tree_traversal(value * 2 + 1, depth - 1));
}

void testGenerator() {
    std::print("Fibonacci: ");
    for (int f : fibonacci(10)) std::print("{} ", f);
    std::println("");
}

// ============================================================================
// 9. std::flat_map/flat_set (C++23)
// ============================================================================

void testFlatContainers() {
    std::flat_map<std::string, int> scores;
    scores["Alice"] = 100;
    scores["Bob"] = 95;
    
    std::flat_set<int> uniqueNums = {5, 3, 8, 1, 9, 2};
    
    for (const auto& [name, score] : scores) {
        std::println("{}: {}", name, score);
    }
}

// ============================================================================
// 10. std::mdspan (C++23)
// ============================================================================

void testMdspan() {
    std::array<int, 12> data = {1,2,3,4,5,6,7,8,9,10,11,12};
    std::mdspan matrix(data.data(), 3, 4);
    
    std::println("3x4 matrix:");
    for (size_t i = 0; i < matrix.extent(0); ++i) {
        for (size_t j = 0; j < matrix.extent(1); ++j) {
            std::print("{:3} ", matrix[i, j]);
        }
        std::println("");
    }
}

// ============================================================================
// 11. std::stacktrace (C++23)
// ============================================================================

void innerFunction() {
    auto trace = std::stacktrace::current();
    std::println("Stack trace ({} frames):", trace.size());
}

// ============================================================================
// 12. std::move_only_function (C++23)
// ============================================================================

void testMoveOnlyFunction() {
    std::move_only_function<int(int)> fn = [ptr = std::make_unique<int>(10)](int x) {
        return *ptr + x;
    };
    std::println("move_only_function: {}", fn(5));
}

// ============================================================================
// 13. [[assume]] (C++23)
// ============================================================================

int processValue(int x) {
    [[assume(x > 0)]];
    return x * 2;
}

// ============================================================================
// 14. std::unreachable() (C++23)
// ============================================================================

int getSign(int x) {
    if (x > 0) return 1;
    if (x < 0) return -1;
    if (x == 0) return 0;
    std::unreachable();
}

// ============================================================================
// 15. std::byteswap (C++23)
// ============================================================================

void testByteswap() {
    uint32_t value = 0x12345678;
    uint32_t swapped = std::byteswap(value);
    std::println("Original: {:08X}, Swapped: {:08X}", value, swapped);
}

// ============================================================================
// 16. std::to_underlying (C++23)
// ============================================================================

enum class Color : uint8_t { Red = 1, Green = 2, Blue = 3 };

void testToUnderlying() {
    auto val = std::to_underlying(Color::Green);
    std::println("Color underlying: {}", val);
}

// ============================================================================
// 17. Optional monadic (C++23)
// ============================================================================

void testOptionalMonadic() {
    std::optional<int> opt = 21;
    auto result = opt
        .and_then([](int x) -> std::optional<int> { return x * 2; })
        .transform([](int x) { return x + 1; })
        .or_else([]() { return std::optional<int>{0}; });
    std::println("Optional monadic: {}", result.value_or(-1));
}

// ============================================================================
// 18. std::spanstream (C++23)
// ============================================================================

void testSpanstream() {
    char buffer[100] = {};
    std::ospanstream oss(std::span<char>(buffer));
    oss << "Hello, " << 42 << "!";
    std::println("Spanstream: {}", buffer);
}

// ============================================================================
// 19. resize_and_overwrite (C++23)
// ============================================================================

void testResizeAndOverwrite() {
    std::string s;
    s.resize_and_overwrite(100, [](char* buf, size_t) {
        for (size_t i = 0; i < 10; ++i) buf[i] = 'A' + i;
        return 10;
    });
    std::println("resize_and_overwrite: {}", s);
}

// ============================================================================
// 20. size_t literal (C++23)
// ============================================================================

void testSizeTLiteral() {
    auto sz = 42uz;
    auto ssz = 42z;
    std::println("size_t: {}, ptrdiff_t: {}", sz, ssz);
}

// ============================================================================
// 21. auto(x) decay (C++23)
// ============================================================================

void testAutoDecay() {
    const int& ref = 42;
    auto copy = auto(ref);
    std::println("auto decay: {}", copy);
}

// ============================================================================
// 22. constexpr unique_ptr (C++23)
// ============================================================================

constexpr int testConstexprUniquePtr() {
    auto ptr = std::make_unique<int>(42);
    return *ptr;
}

// ============================================================================
// 23. Labels at end (C++23)
// ============================================================================

void testLabelsAtEnd() {
    { goto end; end: }
}

// ============================================================================
// 24. Lambda defaults (C++23)
// ============================================================================

void testLambdaDefaults() {
    auto greet = [](std::string name = "World") {
        std::println("Hello, {}!", name);
    };
    greet();
    greet("C++23");
}

// ============================================================================
// 25. static_assert in if constexpr (C++23)
// ============================================================================

template<typename T>
void processType() {
    if constexpr (std::is_integral_v<T>) {
        std::println("Integral");
    } else if constexpr (std::is_floating_point_v<T>) {
        std::println("Float");
    } else {
        static_assert(false, "Unsupported");
    }
}

// ============================================================================
// 26. std::start_lifetime_as (C++23)
// ============================================================================

void testStartLifetimeAs() {
    alignas(int) std::byte storage[sizeof(int)];
    int* p = std::start_lifetime_as<int>(storage);
    *p = 42;
    std::println("start_lifetime_as: {}", *p);
}

// ============================================================================
// MAIN
// ============================================================================

int main() {
    std::println("=== C++23 Feature Test ===");
    
    std::println("\n--- 1. Deducing This ---");
    DeducingThisTest obj;
    std::println("getValue: {}", obj.getValue());
    DeducingThisTest::testRecursiveLambda();
    
    std::println("\n--- 2. Multidimensional [] ---");
    Matrix m(3, 3);
    m[1, 1] = 5.0;
    std::println("m[1,1] = {}", m[1, 1]);
    
    std::println("\n--- 3. if consteval ---");
    constexpr int ct = computeValue(5);
    std::println("consteval: {}", ct);
    
    std::println("\n--- 4. Static operators ---");
    std::println("StaticCallable: {}", StaticCallable{}(3, 4));
    
    std::println("\n--- 5. std::expected ---");
    testExpected();
    
    std::println("\n--- 6. std::print ---");
    testPrint();
    
    std::println("\n--- 7. Ranges C++23 ---");
    testRangesC23();
    
    std::println("\n--- 8. std::generator ---");
    testGenerator();
    
    std::println("\n--- 9. Flat containers ---");
    testFlatContainers();
    
    std::println("\n--- 10. mdspan ---");
    testMdspan();
    
    std::println("\n--- 11. stacktrace ---");
    innerFunction();
    
    std::println("\n--- 12. move_only_function ---");
    testMoveOnlyFunction();
    
    std::println("\n--- 13. [[assume]] ---");
    std::println("processValue: {}", processValue(10));
    
    std::println("\n--- 14. getSign ---");
    std::println("getSign: {}", getSign(5));
    
    std::println("\n--- 15. byteswap ---");
    testByteswap();
    
    std::println("\n--- 16. to_underlying ---");
    testToUnderlying();
    
    std::println("\n--- 17. Optional monadic ---");
    testOptionalMonadic();
    
    std::println("\n--- 18. spanstream ---");
    testSpanstream();
    
    std::println("\n--- 19. resize_and_overwrite ---");
    testResizeAndOverwrite();
    
    std::println("\n--- 20. size_t literal ---");
    testSizeTLiteral();
    
    std::println("\n--- 21. auto decay ---");
    testAutoDecay();
    
    std::println("\n--- 22. constexpr unique_ptr ---");
    constexpr int pv = testConstexprUniquePtr();
    std::println("constexpr unique_ptr: {}", pv);
    
    std::println("\n--- 23. Labels at end ---");
    testLabelsAtEnd();
    std::println("OK");
    
    std::println("\n--- 24. Lambda defaults ---");
    testLambdaDefaults();
    
    std::println("\n--- 25. if constexpr static_assert ---");
    processType<int>();
    processType<double>();
    
    std::println("\n--- 26. start_lifetime_as ---");
    testStartLifetimeAs();
    
    std::println("\n=== All C++23 Tests Complete ===");
    return 0;
}
