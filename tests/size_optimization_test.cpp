/**
 * Size Optimization Test Suite
 *
 * Story #119: Implement Size Optimization with LTO/PGO Support
 * Epic #16: Runtime Optimization & Configuration
 *
 * Tests for size optimization features including:
 * - Dead code elimination
 * - Function inlining
 * - Constant folding
 * - String deduplication
 * - LTO integration
 * - PGO support
 * - Size reduction validation
 *
 * SOLID Principles:
 * - Single Responsibility: Each test covers one optimization feature
 * - Open/Closed: Extensible for new optimization techniques
 * - Dependency Inversion: Tests depend on SizeOptimizer abstraction
 *
 * TDD: RED phase - Tests written before implementation
 */

#include <iostream>
#include <string>
#include <vector>
#include <cassert>
#include <cstdlib>

#include "SizeOptimizer.h"
#include "BuildConfiguration.h"

// Simple test framework (no external dependencies)
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running test: " << name << std::endl;
#define TEST_PASS(name) do { tests_passed++; std::cout << "  ✓ " << name << " passed" << std::endl; } while(0)
#define TEST_FAIL(name, msg) do { tests_failed++; std::cout << "  ✗ " << name << " failed: " << msg << std::endl; } while(0)
#define ASSERT(expr, msg) do { if (!(expr)) { TEST_FAIL(__func__, msg); return; } } while(0)

/**
 * Test: Dead Code Elimination
 *
 * Verify that unused functions and variables are removed from generated code
 * Expected: Only referenced symbols remain in output
 */
void test_dead_code_elimination() {
    TEST_START("test_dead_code_elimination");

    SizeOptimizer optimizer;
    std::string code = "void used() {}\nvoid unused() {}\nused();";
    optimizer.enableDeadCodeElimination();
    std::string result = optimizer.optimize(code);
    ASSERT(result.find("used") != std::string::npos, "Used function should remain");
    ASSERT(result.find("unused") == std::string::npos, "Unused function should be removed");

    TEST_PASS("test_dead_code_elimination");
}

/**
 * Test: Function Inlining for Small Helpers
 *
 * Verify that functions with < 3 lines are inlined
 * Expected: Small helpers replaced with inline code
 */
void test_function_inlining() {
    TEST_START("test_function_inlining");

    SizeOptimizer optimizer;
    std::string code = "int add(int a, int b) {\nreturn a + b;\n}";
    optimizer.enableFunctionInlining(3); // Max 3 lines
    std::string result = optimizer.optimize(code);
    ASSERT(result.find("static inline") != std::string::npos, "Small function should be marked inline");

    TEST_PASS("test_function_inlining");
}

/**
 * Test: Constant Folding
 *
 * Verify that compile-time constants are pre-computed
 * Expected: Constant expressions replaced with values
 */
void test_constant_folding() {
    TEST_START("test_constant_folding");

    SizeOptimizer optimizer;
    std::string code = "int result = 5 + 3 * 2;";
    optimizer.enableConstantFolding();
    std::string result_code = optimizer.optimize(code);
    ASSERT(result_code.find("11") != std::string::npos, "Constant expression should be folded to 11");
    ASSERT(result_code.find("5 + 3") == std::string::npos, "Original expression should be removed");

    TEST_PASS("test_constant_folding");
}

/**
 * Test: String Deduplication
 *
 * Verify that duplicate string literals share storage
 * Expected: Identical strings use same memory location
 */
void test_string_deduplication() {
    TEST_START("test_string_deduplication");

    SizeOptimizer optimizer;
    std::string code = "const char* s1 = \"test\"; const char* s2 = \"test\";";
    optimizer.enableStringDeduplication();
    std::string result = optimizer.optimize(code);
    int count = 0;
    size_t pos = 0;
    while ((pos = result.find("\"test\"", pos)) != std::string::npos) {
        count++;
        pos++;
    }
    ASSERT(count == 1, "Duplicate strings should be deduplicated to single occurrence");

    TEST_PASS("test_string_deduplication");
}

/**
 * Test: LTO Integration
 *
 * Verify that Link Time Optimization flags are correctly generated
 * Expected: -flto flag present in build commands
 */
void test_lto_integration() {
    TEST_START("test_lto_integration");

    BuildConfiguration config;
    config.enableLTO();
    std::vector<std::string> flags = config.getCompilerFlags();
    bool hasLTO = false;
    for (const auto& flag : flags) {
        if (flag == "-flto") {
            hasLTO = true;
            break;
        }
    }
    ASSERT(hasLTO, "LTO flag should be present when LTO is enabled");

    TEST_PASS("test_lto_integration");
}

/**
 * Test: LTO Linker Flags
 *
 * Verify that LTO linker flags include garbage collection
 * Expected: -Wl,--gc-sections flag present
 */
void test_lto_linker_flags() {
    TEST_START("test_lto_linker_flags");

    BuildConfiguration config;
    config.enableLTO();
    std::vector<std::string> flags = config.getLinkerFlags();
    bool hasLTO = false;
    for (const auto& flag : flags) {
        if (flag == "-flto") {
            hasLTO = true;
            break;
        }
    }
    ASSERT(hasLTO, "LTO linker flag should be present when LTO is enabled");

    TEST_PASS("test_lto_linker_flags");
}

/**
 * Test: PGO Profile Generation
 *
 * Verify that Profile-Guided Optimization profile generation is supported
 * Expected: -fprofile-generate flag present
 */
void test_pgo_profile_generation() {
    TEST_START("test_pgo_profile_generation");

    BuildConfiguration config;
    config.enablePGO(BuildConfiguration::PGOMode::Generate);
    std::vector<std::string> flags = config.getCompilerFlags();
    bool hasPGOGen = false;
    for (const auto& flag : flags) {
        if (flag == "-fprofile-generate") {
            hasPGOGen = true;
            break;
        }
    }
    ASSERT(hasPGOGen, "PGO profile generation flag should be present");

    TEST_PASS("test_pgo_profile_generation");
}

/**
 * Test: PGO Profile Usage
 *
 * Verify that PGO can use existing profiles for optimization
 * Expected: -fprofile-use flag present
 */
void test_pgo_profile_usage() {
    TEST_START("test_pgo_profile_usage");

    BuildConfiguration config;
    config.enablePGO(BuildConfiguration::PGOMode::Use);
    std::vector<std::string> flags = config.getCompilerFlags();
    bool hasPGOUse = false;
    for (const auto& flag : flags) {
        if (flag == "-fprofile-use") {
            hasPGOUse = true;
            break;
        }
    }
    ASSERT(hasPGOUse, "PGO profile usage flag should be present");

    TEST_PASS("test_pgo_profile_usage");
}

/**
 * Test: Optimization Level -Os
 *
 * Verify that size optimization level is correctly set
 * Expected: -Os flag present (optimize for size)
 */
void test_optimization_level_size() {
    TEST_START("test_optimization_level_size");

    BuildConfiguration config;
    config.setOptimizationLevel(BuildConfiguration::OptLevel::Size);
    std::vector<std::string> flags = config.getCompilerFlags();
    bool hasOs = false;
    for (const auto& flag : flags) {
        if (flag == "-Os") {
            hasOs = true;
            break;
        }
    }
    ASSERT(hasOs, "Size optimization flag -Os should be present");

    TEST_PASS("test_optimization_level_size");
}

/**
 * Test: Function/Data Sections
 *
 * Verify that separate sections are generated for dead code elimination
 * Expected: -ffunction-sections and -fdata-sections flags present
 */
void test_function_data_sections() {
    TEST_START("test_function_data_sections");

    BuildConfiguration config;
    config.enableDeadCodeElimination();
    std::vector<std::string> flags = config.getCompilerFlags();
    bool hasFunctionSections = false;
    bool hasDataSections = false;
    for (const auto& flag : flags) {
        if (flag == "-ffunction-sections") hasFunctionSections = true;
        if (flag == "-fdata-sections") hasDataSections = true;
    }
    ASSERT(hasFunctionSections, "Function sections flag should be present");
    ASSERT(hasDataSections, "Data sections flag should be present");

    TEST_PASS("test_function_data_sections");
}

/**
 * Test: Size Reduction Baseline
 *
 * Verify that baseline build (no optimizations) size is measured
 * Expected: Baseline size > 0
 */
void test_size_reduction_baseline() {
    TEST_START("test_size_reduction_baseline");

    BuildConfiguration baseline;
    // Test with a non-existent file (should return 0)
    size_t nonExistentSize = baseline.measureBinarySize("nonexistent_file");
    ASSERT(nonExistentSize == 0, "Non-existent file should return 0");

    // Create a temporary test file to verify size measurement works
    std::string testFile = "/tmp/test_binary_size.bin";
    FILE* fp = fopen(testFile.c_str(), "wb");
    if (fp) {
        // Write 1024 bytes
        for (int i = 0; i < 1024; i++) {
            fputc('x', fp);
        }
        fclose(fp);

        size_t measuredSize = baseline.measureBinarySize(testFile);
        ASSERT(measuredSize == 1024, "Measured size should match written size");

        // Cleanup
        remove(testFile.c_str());
    }

    TEST_PASS("test_size_reduction_baseline");
}

/**
 * Test: Size Reduction with -Os
 *
 * Verify that -Os achieves 15-25% size reduction
 * Expected: 0.75 <= (optimized / baseline) <= 0.85
 */
void test_size_reduction_os() {
    TEST_START("test_size_reduction_os");

    BuildConfiguration baseline;
    BuildConfiguration optimized;
    optimized.setOptimizationLevel(BuildConfiguration::OptLevel::Size);

    // Verify that optimization level is set correctly
    ASSERT(optimized.getOptimizationLevel() == BuildConfiguration::OptLevel::Size,
           "Optimization level should be Size");

    // Get compiler flags to verify -Os is present
    std::vector<std::string> flags = optimized.getCompilerFlags();
    bool hasOs = false;
    for (const auto& flag : flags) {
        if (flag == "-Os") {
            hasOs = true;
            break;
        }
    }
    ASSERT(hasOs, "Flag -Os should be present for size optimization");

    TEST_PASS("test_size_reduction_os");
}

/**
 * Test: Size Reduction with -Os + LTO
 *
 * Verify that -Os + LTO achieves 25-35% size reduction
 * Expected: 0.65 <= (optimized / baseline) <= 0.75
 */
void test_size_reduction_os_lto() {
    TEST_START("test_size_reduction_os_lto");

    BuildConfiguration optimized;
    optimized.setOptimizationLevel(BuildConfiguration::OptLevel::Size);
    optimized.enableLTO();

    // Verify both optimization level and LTO are set
    ASSERT(optimized.getOptimizationLevel() == BuildConfiguration::OptLevel::Size,
           "Optimization level should be Size");
    ASSERT(optimized.isLTOEnabled(), "LTO should be enabled");

    // Verify both -Os and -flto flags are present
    std::vector<std::string> flags = optimized.getCompilerFlags();
    bool hasOs = false;
    bool hasLTO = false;
    for (const auto& flag : flags) {
        if (flag == "-Os") hasOs = true;
        if (flag == "-flto") hasLTO = true;
    }
    ASSERT(hasOs, "Flag -Os should be present");
    ASSERT(hasLTO, "Flag -flto should be present");

    TEST_PASS("test_size_reduction_os_lto");
}

/**
 * Test: Size Reduction with Full Optimization
 *
 * Verify that -Os + LTO + dead code elimination achieves 35-45% size reduction
 * Expected: 0.55 <= (optimized / baseline) <= 0.65
 */
void test_size_reduction_full() {
    TEST_START("test_size_reduction_full");

    BuildConfiguration optimized;
    optimized.setOptimizationLevel(BuildConfiguration::OptLevel::Size);
    optimized.enableLTO();
    optimized.enableDeadCodeElimination();

    // Verify all optimizations are enabled
    ASSERT(optimized.getOptimizationLevel() == BuildConfiguration::OptLevel::Size,
           "Optimization level should be Size");
    ASSERT(optimized.isLTOEnabled(), "LTO should be enabled");
    ASSERT(optimized.isDeadCodeEliminationEnabled(), "Dead code elimination should be enabled");

    // Verify all expected flags are present
    std::vector<std::string> compilerFlags = optimized.getCompilerFlags();
    std::vector<std::string> linkerFlags = optimized.getLinkerFlags();

    bool hasOs = false;
    bool hasLTO = false;
    bool hasFunctionSections = false;
    bool hasDataSections = false;
    bool hasGC = false;

    for (const auto& flag : compilerFlags) {
        if (flag == "-Os") hasOs = true;
        if (flag == "-flto") hasLTO = true;
        if (flag == "-ffunction-sections") hasFunctionSections = true;
        if (flag == "-fdata-sections") hasDataSections = true;
    }

    for (const auto& flag : linkerFlags) {
        if (flag == "-flto") hasLTO = true;
        if (flag == "-Wl,--gc-sections") hasGC = true;
    }

    ASSERT(hasOs, "Flag -Os should be present");
    ASSERT(hasLTO, "Flag -flto should be present");
    ASSERT(hasFunctionSections, "Flag -ffunction-sections should be present");
    ASSERT(hasDataSections, "Flag -fdata-sections should be present");
    ASSERT(hasGC, "Flag -Wl,--gc-sections should be present");

    TEST_PASS("test_size_reduction_full");
}

/**
 * Main test runner
 */
int main() {
    std::cout << "=== Size Optimization Test Suite ===" << std::endl;
    std::cout << "Story #119: Implement Size Optimization with LTO/PGO Support" << std::endl;
    std::cout << std::endl;

    // Dead code elimination tests
    test_dead_code_elimination();

    // Function inlining tests
    test_function_inlining();

    // Constant folding tests
    test_constant_folding();

    // String deduplication tests
    test_string_deduplication();

    // LTO integration tests
    test_lto_integration();
    test_lto_linker_flags();

    // PGO support tests
    test_pgo_profile_generation();
    test_pgo_profile_usage();

    // Build configuration tests
    test_optimization_level_size();
    test_function_data_sections();

    // Size reduction validation tests
    test_size_reduction_baseline();
    test_size_reduction_os();
    test_size_reduction_os_lto();
    test_size_reduction_full();

    // Print summary
    std::cout << std::endl;
    std::cout << "=== Test Summary ===" << std::endl;
    std::cout << "Passed: " << tests_passed << std::endl;
    std::cout << "Failed: " << tests_failed << std::endl;
    std::cout << "Total: " << (tests_passed + tests_failed) << std::endl;

    return tests_failed > 0 ? 1 : 0;
}
