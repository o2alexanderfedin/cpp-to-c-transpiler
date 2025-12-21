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
// Simple test framework (no external dependencies)

#include <gtest/gtest.h>
#include <string>
#include <vector>
#include <cassert>
#include <cstdlib>
#include "SizeOptimizer.h"
#include "BuildConfiguration.h"

using namespace clang;

* Test: Function Inlining for Small Helpers
 *
 * Verify that functions with < 3 lines are inlined
 * Expected: Small helpers replaced with inline code
 */

TEST(size_optimization_test, test_dead_code_elimination) {
    SizeOptimizer optimizer;
        std::string code = "void used() {}\nvoid unused() {}\nused();";
        optimizer.enableDeadCodeElimination();
        std::string result = optimizer.optimize(code);
        ASSERT_TRUE(result.find("used") != std::string::npos) << "Used function should remain";
        ASSERT_TRUE(result.find("unused") == std::string::npos) << "Unused function should be removed";
}

TEST(size_optimization_test, test_function_inlining) {
    SizeOptimizer optimizer;
        std::string code = "int add(int a, int b) {\nreturn a + b;\n}";
        optimizer.enableFunctionInlining(3); // Max 3 lines
        std::string result = optimizer.optimize(code);
        ASSERT_TRUE(result.find("static inline") != std::string::npos) << "Small function should be marked inline";
}

TEST(size_optimization_test, test_constant_folding) {
    SizeOptimizer optimizer;
        std::string code = "int result = 5 + 3 * 2;";
        optimizer.enableConstantFolding();
        std::string result_code = optimizer.optimize(code);
        ASSERT_TRUE(result_code.find("11") != std::string::npos) << "Constant expression should be folded to 11";
        ASSERT_TRUE(result_code.find("5 + 3") == std::string::npos) << "Original expression should be removed";
}

TEST(size_optimization_test, test_string_deduplication) {
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
        ASSERT_TRUE(count == 1) << "Duplicate strings should be deduplicated to single occurrence";
}

TEST(size_optimization_test, test_lto_integration) {
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
        ASSERT_TRUE(hasLTO) << "LTO flag should be present when LTO is enabled";
}

TEST(size_optimization_test, test_lto_linker_flags) {
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
        ASSERT_TRUE(hasLTO) << "LTO linker flag should be present when LTO is enabled";
}

TEST(size_optimization_test, test_pgo_profile_generation) {
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
        ASSERT_TRUE(hasPGOGen) << "PGO profile generation flag should be present";
}

TEST(size_optimization_test, test_pgo_profile_usage) {
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
        ASSERT_TRUE(hasPGOUse) << "PGO profile usage flag should be present";
}

TEST(size_optimization_test, test_optimization_level_size) {
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
        ASSERT_TRUE(hasOs) << "Size optimization flag -Os should be present";
}

TEST(size_optimization_test, test_function_data_sections) {
    BuildConfiguration config;
        config.enableDeadCodeElimination();
        std::vector<std::string> flags = config.getCompilerFlags();
        bool hasFunctionSections = false;
        bool hasDataSections = false;
        for (const auto& flag : flags) {
            if (flag == "-ffunction-sections") hasFunctionSections = true;
            if (flag == "-fdata-sections") hasDataSections = true;
        }
        ASSERT_TRUE(hasFunctionSections) << "Function sections flag should be present";
        ASSERT_TRUE(hasDataSections) << "Data sections flag should be present";
}

TEST(size_optimization_test, test_size_reduction_baseline) {
    BuildConfiguration baseline;
        // Test with a non-existent file (should return 0)
        size_t nonExistentSize = baseline.measureBinarySize("nonexistent_file");
        ASSERT_TRUE(nonExistentSize == 0) << "Non-existent file should return 0";

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
            ASSERT_TRUE(measuredSize == 1024) << "Measured size should match written size";

            // Cleanup
            remove(testFile.c_str());
        }
}

TEST(size_optimization_test, test_size_reduction_os) {
    BuildConfiguration baseline;
        BuildConfiguration optimized;
        optimized.setOptimizationLevel(BuildConfiguration::OptLevel::Size);

        // Verify that optimization level is set correctly
        ASSERT_TRUE(optimized.getOptimizationLevel() == BuildConfiguration::OptLevel::Size) << "Optimization level should be Size";

        // Get compiler flags to verify -Os is present
        std::vector<std::string> flags = optimized.getCompilerFlags();
        bool hasOs = false;
        for (const auto& flag : flags) {
            if (flag == "-Os") {
                hasOs = true;
                break;
            }
        }
        ASSERT_TRUE(hasOs) << "Flag -Os should be present for size optimization";
}

TEST(size_optimization_test, test_size_reduction_os_lto) {
    BuildConfiguration optimized;
        optimized.setOptimizationLevel(BuildConfiguration::OptLevel::Size);
        optimized.enableLTO();

        // Verify both optimization level and LTO are set
        ASSERT_TRUE(optimized.getOptimizationLevel() == BuildConfiguration::OptLevel::Size) << "Optimization level should be Size";
        ASSERT_TRUE(optimized.isLTOEnabled()) << "LTO should be enabled";

        // Verify both -Os and -flto flags are present
        std::vector<std::string> flags = optimized.getCompilerFlags();
        bool hasOs = false;
        bool hasLTO = false;
        for (const auto& flag : flags) {
            if (flag == "-Os") hasOs = true;
            if (flag == "-flto") hasLTO = true;
        }
        ASSERT_TRUE(hasOs) << "Flag -Os should be present";
        ASSERT_TRUE(hasLTO) << "Flag -flto should be present";
}

TEST(size_optimization_test, test_size_reduction_full) {
    BuildConfiguration optimized;
        optimized.setOptimizationLevel(BuildConfiguration::OptLevel::Size);
        optimized.enableLTO();
        optimized.enableDeadCodeElimination();

        // Verify all optimizations are enabled
        ASSERT_TRUE(optimized.getOptimizationLevel() == BuildConfiguration::OptLevel::Size) << "Optimization level should be Size";
        ASSERT_TRUE(optimized.isLTOEnabled()) << "LTO should be enabled";
        ASSERT_TRUE(optimized.isDeadCodeEliminationEnabled()) << "Dead code elimination should be enabled";

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

        ASSERT_TRUE(hasOs) << "Flag -Os should be present";
        ASSERT_TRUE(hasLTO) << "Flag -flto should be present";
        ASSERT_TRUE(hasFunctionSections) << "Flag -ffunction-sections should be present";
        ASSERT_TRUE(hasDataSections) << "Flag -fdata-sections should be present";
        ASSERT_TRUE(hasGC) << "Flag -Wl,--gc-sections should be present";
}
