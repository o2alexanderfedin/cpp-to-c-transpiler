// tests/gtest/SizeOptimizationTest_GTest.cpp
// Unit tests for size optimization with LTO/PGO support (Story #119)
// Migrated to Google Test framework
//
// Tests for size optimization features including:
// - Dead code elimination
// - Function inlining
// - Constant folding
// - String deduplication
// - LTO integration
// - PGO support
// - Size reduction validation with performance benchmarks

#include "../../include/BuildConfiguration.h"
#include "../../include/SizeOptimizer.h"
#include <cstdio>
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace std;

// Test fixture for SizeOptimizer tests
class SizeOptimizerTest : public ::testing::Test {
protected:
  SizeOptimizer optimizer;

  void SetUp() override { optimizer = SizeOptimizer(); }
};

// Test fixture for BuildConfiguration tests
class BuildConfigurationTest : public ::testing::Test {
protected:
  BuildConfiguration config;

  void SetUp() override { config = BuildConfiguration(); }
};

// ============================================================================
// Dead Code Elimination Tests
// ============================================================================

TEST_F(SizeOptimizerTest, DeadCodeElimination) {
  string code = "void used() {}\nvoid unused() {}\nused();";
  optimizer.enableDeadCodeElimination();
  string result = optimizer.optimize(code);

  EXPECT_NE(result.find("used"), string::npos) << "Used function should remain";
  EXPECT_EQ(result.find("unused"), string::npos)
      << "Unused function should be removed";
}

// ============================================================================
// Function Inlining Tests
// ============================================================================

TEST_F(SizeOptimizerTest, FunctionInlining) {
  string code = "int add(int a, int b) {\nreturn a + b;\n}";
  optimizer.enableFunctionInlining(3); // Max 3 lines
  string result = optimizer.optimize(code);

  EXPECT_NE(result.find("static inline"), string::npos)
      << "Small function should be marked inline";
}

// ============================================================================
// Constant Folding Tests
// ============================================================================

TEST_F(SizeOptimizerTest, ConstantFolding) {
  string code = "int result = 5 + 3 * 2;";
  optimizer.enableConstantFolding();
  string result_code = optimizer.optimize(code);

  EXPECT_NE(result_code.find("11"), string::npos)
      << "Constant expression should be folded to 11";
  EXPECT_EQ(result_code.find("5 + 3"), string::npos)
      << "Original expression should be removed";
}

// ============================================================================
// String Deduplication Tests
// ============================================================================

TEST_F(SizeOptimizerTest, StringDeduplication) {
  string code = "const char* s1 = \"test\"; const char* s2 = \"test\";";
  optimizer.enableStringDeduplication();
  string result = optimizer.optimize(code);

  int count = 0;
  size_t pos = 0;
  while ((pos = result.find("\"test\"", pos)) != string::npos) {
    count++;
    pos++;
  }
  EXPECT_EQ(count, 1)
      << "Duplicate strings should be deduplicated to single occurrence";
}

// ============================================================================
// LTO Integration Tests
// ============================================================================

TEST_F(BuildConfigurationTest, LTOIntegration) {
  config.enableLTO();
  vector<string> flags = config.getCompilerFlags();

  bool hasLTO = false;
  for (const auto &flag : flags) {
    if (flag == "-flto") {
      hasLTO = true;
      break;
    }
  }
  EXPECT_TRUE(hasLTO) << "LTO flag should be present when LTO is enabled";
}

TEST_F(BuildConfigurationTest, LTOLinkerFlags) {
  config.enableLTO();
  vector<string> flags = config.getLinkerFlags();

  bool hasLTO = false;
  for (const auto &flag : flags) {
    if (flag == "-flto") {
      hasLTO = true;
      break;
    }
  }
  EXPECT_TRUE(hasLTO)
      << "LTO linker flag should be present when LTO is enabled";
}

// ============================================================================
// PGO Support Tests
// ============================================================================

TEST_F(BuildConfigurationTest, PGOProfileGeneration) {
  config.enablePGO(BuildConfiguration::PGOMode::Generate);
  vector<string> flags = config.getCompilerFlags();

  bool hasPGOGen = false;
  for (const auto &flag : flags) {
    if (flag == "-fprofile-generate") {
      hasPGOGen = true;
      break;
    }
  }
  EXPECT_TRUE(hasPGOGen) << "PGO profile generation flag should be present";
}

TEST_F(BuildConfigurationTest, PGOProfileUsage) {
  config.enablePGO(BuildConfiguration::PGOMode::Use);
  vector<string> flags = config.getCompilerFlags();

  bool hasPGOUse = false;
  for (const auto &flag : flags) {
    if (flag == "-fprofile-use") {
      hasPGOUse = true;
      break;
    }
  }
  EXPECT_TRUE(hasPGOUse) << "PGO profile usage flag should be present";
}

// ============================================================================
// Optimization Level Tests
// ============================================================================

TEST_F(BuildConfigurationTest, OptimizationLevelSize) {
  config.setOptimizationLevel(BuildConfiguration::OptLevel::Size);
  vector<string> flags = config.getCompilerFlags();

  bool hasOs = false;
  for (const auto &flag : flags) {
    if (flag == "-Os") {
      hasOs = true;
      break;
    }
  }
  EXPECT_TRUE(hasOs) << "Size optimization flag -Os should be present";
}

TEST_F(BuildConfigurationTest, FunctionDataSections) {
  config.enableDeadCodeElimination();
  vector<string> flags = config.getCompilerFlags();

  bool hasFunctionSections = false;
  bool hasDataSections = false;
  for (const auto &flag : flags) {
    if (flag == "-ffunction-sections")
      hasFunctionSections = true;
    if (flag == "-fdata-sections")
      hasDataSections = true;
  }
  EXPECT_TRUE(hasFunctionSections)
      << "Function sections flag should be present";
  EXPECT_TRUE(hasDataSections) << "Data sections flag should be present";
}

// ============================================================================
// Size Reduction Validation Tests (Performance Benchmarks)
// ============================================================================

TEST_F(BuildConfigurationTest, SizeReductionBaseline) {
  // Test with a non-existent file (should return 0)
  size_t nonExistentSize = config.measureBinarySize("nonexistent_file");
  EXPECT_EQ(nonExistentSize, 0) << "Non-existent file should return 0";

  // Create a temporary test file to verify size measurement works
  string testFile = "/tmp/test_binary_size.bin";
  FILE *fp = fopen(testFile.c_str(), "wb");
  if (fp) {
    // Write 1024 bytes
    for (int i = 0; i < 1024; i++) {
      fputc('x', fp);
    }
    fclose(fp);

    size_t measuredSize = config.measureBinarySize(testFile);
    EXPECT_EQ(measuredSize, 1024) << "Measured size should match written size";

    // Cleanup
    remove(testFile.c_str());
  }
}

TEST_F(BuildConfigurationTest, SizeReductionWithOptimizationLevelSize) {
  BuildConfiguration optimized;
  optimized.setOptimizationLevel(BuildConfiguration::OptLevel::Size);

  // Verify that optimization level is set correctly
  EXPECT_EQ(optimized.getOptimizationLevel(),
            BuildConfiguration::OptLevel::Size)
      << "Optimization level should be Size";

  // Get compiler flags to verify -Os is present
  vector<string> flags = optimized.getCompilerFlags();
  bool hasOs = false;
  for (const auto &flag : flags) {
    if (flag == "-Os") {
      hasOs = true;
      break;
    }
  }
  EXPECT_TRUE(hasOs) << "Flag -Os should be present for size optimization";
}

TEST_F(BuildConfigurationTest, SizeReductionWithOsAndLTO) {
  BuildConfiguration optimized;
  optimized.setOptimizationLevel(BuildConfiguration::OptLevel::Size);
  optimized.enableLTO();

  // Verify both optimization level and LTO are set
  EXPECT_EQ(optimized.getOptimizationLevel(),
            BuildConfiguration::OptLevel::Size)
      << "Optimization level should be Size";
  EXPECT_TRUE(optimized.isLTOEnabled()) << "LTO should be enabled";

  // Verify both -Os and -flto flags are present
  vector<string> flags = optimized.getCompilerFlags();
  bool hasOs = false;
  bool hasLTO = false;
  for (const auto &flag : flags) {
    if (flag == "-Os")
      hasOs = true;
    if (flag == "-flto")
      hasLTO = true;
  }
  EXPECT_TRUE(hasOs) << "Flag -Os should be present";
  EXPECT_TRUE(hasLTO) << "Flag -flto should be present";
}

TEST_F(BuildConfigurationTest, SizeReductionFull) {
  BuildConfiguration optimized;
  optimized.setOptimizationLevel(BuildConfiguration::OptLevel::Size);
  optimized.enableLTO();
  optimized.enableDeadCodeElimination();

  // Verify all optimizations are enabled
  EXPECT_EQ(optimized.getOptimizationLevel(),
            BuildConfiguration::OptLevel::Size)
      << "Optimization level should be Size";
  EXPECT_TRUE(optimized.isLTOEnabled()) << "LTO should be enabled";
  EXPECT_TRUE(optimized.isDeadCodeEliminationEnabled())
      << "Dead code elimination should be enabled";

  // Verify all expected flags are present
  vector<string> compilerFlags = optimized.getCompilerFlags();
  vector<string> linkerFlags = optimized.getLinkerFlags();

  bool hasOs = false;
  bool hasLTO = false;
  bool hasFunctionSections = false;
  bool hasDataSections = false;
  bool hasGC = false;

  for (const auto &flag : compilerFlags) {
    if (flag == "-Os")
      hasOs = true;
    if (flag == "-flto")
      hasLTO = true;
    if (flag == "-ffunction-sections")
      hasFunctionSections = true;
    if (flag == "-fdata-sections")
      hasDataSections = true;
  }

  for (const auto &flag : linkerFlags) {
    if (flag == "-flto")
      hasLTO = true;
    if (flag == "-Wl,--gc-sections")
      hasGC = true;
  }

  EXPECT_TRUE(hasOs) << "Flag -Os should be present";
  EXPECT_TRUE(hasLTO) << "Flag -flto should be present";
  EXPECT_TRUE(hasFunctionSections)
      << "Flag -ffunction-sections should be present";
  EXPECT_TRUE(hasDataSections) << "Flag -fdata-sections should be present";
  EXPECT_TRUE(hasGC) << "Flag -Wl,--gc-sections should be present";
}

// Test 13: Disable optimization when not needed
TEST_F(BuildConfigurationTest, DisableOptimization) {
  BuildConfiguration config;
  config.setOptimizationLevel(BuildConfiguration::OptLevel::None);

  vector<string> flags = config.getCompilerFlags();

  bool hasOs = false;
  for (const auto &flag : flags) {
    if (flag == "-Os")
      hasOs = true;
  }
  EXPECT_FALSE(hasOs) << "Size optimization flag should not be present when optimization is disabled";
}
