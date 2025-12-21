// tests/gtest/RuntimeFeatureFlagsTest_GTest.cpp
// Unit tests for modular runtime feature flags (Story #118)
// Migrated to Google Test framework
//
// This test suite validates command-line flag parsing for runtime features,
// allowing users to enable only the features they need (exceptions, RTTI,
// coroutines, virtual inheritance).

#include "../../include/RuntimeFeatureFlags.h"
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace std;

// Test fixture for RuntimeFeatureFlags tests
class RuntimeFeatureFlagsTest : public ::testing::Test {
protected:
  // Helper to create flags object from arguments
  unique_ptr<RuntimeFeatureFlags> createFlags(vector<const char *> &args) {
    return make_unique<RuntimeFeatureFlags>(
        args.size(), const_cast<const char **>(args.data()));
  }
};

// Test 1: Parse single exception flag
TEST_F(RuntimeFeatureFlagsTest, ParseExceptionsFlag) {
  vector<const char *> args = {"cpptoc", "--runtime=exceptions", "input.cpp"};
  auto flags = createFlags(args);

  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::Exceptions))
      << "Exceptions should be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::RTTI))
      << "RTTI should NOT be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::Memory))
      << "Memory should NOT be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::VInherit))
      << "VInherit should NOT be enabled";
}

// Test 2: Parse single RTTI flag
TEST_F(RuntimeFeatureFlagsTest, ParseRTTIFlag) {
  vector<const char *> args = {"cpptoc", "--runtime=rtti", "input.cpp"};
  auto flags = createFlags(args);

  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::Exceptions))
      << "Exceptions should NOT be enabled";
  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::RTTI))
      << "RTTI should be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::Memory))
      << "Memory should NOT be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::VInherit))
      << "VInherit should NOT be enabled";
}

// Test 3: Parse single coroutines flag
TEST_F(RuntimeFeatureFlagsTest, ParseCoroutinesFlag) {
  vector<const char *> args = {"cpptoc", "--runtime=coroutines", "input.cpp"};
  auto flags = createFlags(args);

  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::Exceptions))
      << "Exceptions should NOT be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::RTTI))
      << "RTTI should NOT be enabled";
  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::Memory))
      << "Memory should be enabled for coroutines";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::VInherit))
      << "VInherit should NOT be enabled";
}

// Test 4: Parse single vinherit flag
TEST_F(RuntimeFeatureFlagsTest, ParseVInheritFlag) {
  vector<const char *> args = {"cpptoc", "--runtime=vinherit", "input.cpp"};
  auto flags = createFlags(args);

  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::Exceptions))
      << "Exceptions should NOT be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::RTTI))
      << "RTTI should NOT be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::Memory))
      << "Memory should NOT be enabled";
  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::VInherit))
      << "VInherit should be enabled";
}

// Test 5: Parse multiple features (comma-separated)
TEST_F(RuntimeFeatureFlagsTest, ParseMultipleFeatures) {
  vector<const char *> args = {"cpptoc", "--runtime=exceptions,rtti",
                               "input.cpp"};
  auto flags = createFlags(args);

  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::Exceptions))
      << "Exceptions should be enabled";
  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::RTTI))
      << "RTTI should be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::Memory))
      << "Memory should NOT be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::VInherit))
      << "VInherit should NOT be enabled";
}

// Test 6: Parse --runtime=all flag
TEST_F(RuntimeFeatureFlagsTest, ParseAllFlag) {
  vector<const char *> args = {"cpptoc", "--runtime=all", "input.cpp"};
  auto flags = createFlags(args);

  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::Exceptions))
      << "All features: Exceptions should be enabled";
  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::RTTI))
      << "All features: RTTI should be enabled";
  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::Memory))
      << "All features: Memory should be enabled";
  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::VInherit))
      << "All features: VInherit should be enabled";
}

// Test 7: Parse --runtime=none flag
TEST_F(RuntimeFeatureFlagsTest, ParseNoneFlag) {
  vector<const char *> args = {"cpptoc", "--runtime=none", "input.cpp"};
  auto flags = createFlags(args);

  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::Exceptions))
      << "None: Exceptions should NOT be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::RTTI))
      << "None: RTTI should NOT be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::Memory))
      << "None: Memory should NOT be enabled";
  EXPECT_FALSE(flags->isEnabled(RuntimeFeature::VInherit))
      << "None: VInherit should NOT be enabled";
}

// Test 8: Default behavior (no --runtime flag)
TEST_F(RuntimeFeatureFlagsTest, DefaultBehavior) {
  vector<const char *> args = {"cpptoc", "input.cpp"};
  auto flags = createFlags(args);

  // Default: all features enabled (backward compatibility)
  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::Exceptions))
      << "Default: Exceptions should be enabled";
  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::RTTI))
      << "Default: RTTI should be enabled";
  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::Memory))
      << "Default: Memory should be enabled";
  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::VInherit))
      << "Default: VInherit should be enabled";
}

// Test 9: Get enabled features list
TEST_F(RuntimeFeatureFlagsTest, GetEnabledFeatures) {
  vector<const char *> args = {"cpptoc", "--runtime=exceptions,rtti",
                               "input.cpp"};
  auto flags = createFlags(args);

  auto enabled = flags->getEnabledFeatures();
  EXPECT_EQ(enabled.size(), 2) << "Should have exactly 2 enabled features";

  bool hasExceptions = false;
  bool hasRTTI = false;
  for (auto feature : enabled) {
    if (feature == RuntimeFeature::Exceptions)
      hasExceptions = true;
    if (feature == RuntimeFeature::RTTI)
      hasRTTI = true;
  }
  EXPECT_TRUE(hasExceptions) << "Enabled list should contain Exceptions";
  EXPECT_TRUE(hasRTTI) << "Enabled list should contain RTTI";
}

// Test 10: Get module size estimate
TEST_F(RuntimeFeatureFlagsTest, GetModuleSize) {
  RuntimeFeatureFlags flags(0, nullptr); // Default constructor

  // Verify size estimates are reasonable
  size_t exceptionSize = flags.getModuleSize(RuntimeFeature::Exceptions);
  size_t rttiSize = flags.getModuleSize(RuntimeFeature::RTTI);
  size_t memorySize = flags.getModuleSize(RuntimeFeature::Memory);
  size_t vinheritSize = flags.getModuleSize(RuntimeFeature::VInherit);

  EXPECT_GE(exceptionSize, 800)
      << "Exception module size should be at least 800 bytes";
  EXPECT_LE(exceptionSize, 1200)
      << "Exception module size should be at most 1200 bytes";
  EXPECT_GE(rttiSize, 600) << "RTTI module size should be at least 600 bytes";
  EXPECT_LE(rttiSize, 1000) << "RTTI module size should be at most 1000 bytes";
  EXPECT_GE(memorySize, 400)
      << "Memory module size should be at least 400 bytes";
  EXPECT_LE(memorySize, 800)
      << "Memory module size should be at most 800 bytes";
  EXPECT_GE(vinheritSize, 500)
      << "VInherit module size should be at least 500 bytes";
  EXPECT_LE(vinheritSize, 900)
      << "VInherit module size should be at most 900 bytes";
}

// Test 11: Get total enabled size
TEST_F(RuntimeFeatureFlagsTest, GetTotalEnabledSize) {
  vector<const char *> args = {"cpptoc", "--runtime=exceptions,rtti",
                               "input.cpp"};
  auto flags = createFlags(args);

  size_t totalSize = flags->getTotalEnabledSize();

  // Should be sum of exception + RTTI sizes (approx 1400-2200 bytes)
  EXPECT_GE(totalSize, 1400)
      << "Total size should be at least sum of enabled modules";
  EXPECT_LE(totalSize, 2200) << "Total size should be reasonable";
}

// Test 12: Generate preprocessor defines
TEST_F(RuntimeFeatureFlagsTest, GeneratePreprocessorDefines) {
  vector<const char *> args = {"cpptoc", "--runtime=exceptions,rtti",
                               "input.cpp"};
  auto flags = createFlags(args);

  string defines = flags->generatePreprocessorDefines();

  // Should contain #define for enabled features
  EXPECT_NE(defines.find("#define CPPTOC_RUNTIME_EXCEPTIONS"), string::npos)
      << "Should define CPPTOC_RUNTIME_EXCEPTIONS";
  EXPECT_NE(defines.find("#define CPPTOC_RUNTIME_RTTI"), string::npos)
      << "Should define CPPTOC_RUNTIME_RTTI";

  // Should NOT contain defines for disabled features
  EXPECT_EQ(defines.find("#define CPPTOC_RUNTIME_COROUTINES"), string::npos)
      << "Should NOT define CPPTOC_RUNTIME_COROUTINES";
  EXPECT_EQ(defines.find("#define CPPTOC_RUNTIME_VINHERIT"), string::npos)
      << "Should NOT define CPPTOC_RUNTIME_VINHERIT";
}

// Test 13: Invalid feature name handling
TEST_F(RuntimeFeatureFlagsTest, InvalidFeatureName) {
  vector<const char *> args = {"cpptoc", "--runtime=invalid", "input.cpp"};

  EXPECT_THROW(
      { auto flags = createFlags(args); }, invalid_argument)
      << "Should throw exception for invalid feature";
}

// Test 14: Case-insensitive feature names
TEST_F(RuntimeFeatureFlagsTest, CaseInsensitiveNames) {
  vector<const char *> args = {"cpptoc", "--runtime=EXCEPTIONS,Rtti",
                               "input.cpp"};
  auto flags = createFlags(args);

  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::Exceptions))
      << "EXCEPTIONS (uppercase) should be enabled";
  EXPECT_TRUE(flags->isEnabled(RuntimeFeature::RTTI))
      << "Rtti (mixed case) should be enabled";
}

// Test 15: Module size documentation
TEST_F(RuntimeFeatureFlagsTest, GenerateSizeDocumentation) {
  RuntimeFeatureFlags flags(0, nullptr);

  string sizeDoc = flags.generateSizeDocumentation();

  // Should contain documentation for all modules
  EXPECT_TRUE(sizeDoc.find("exceptions") != string::npos ||
              sizeDoc.find("Exceptions") != string::npos)
      << "Should document exceptions module";
  EXPECT_TRUE(sizeDoc.find("rtti") != string::npos ||
              sizeDoc.find("RTTI") != string::npos)
      << "Should document RTTI module";
  EXPECT_NE(sizeDoc.find("bytes"), string::npos)
      << "Should include size in bytes";
}
