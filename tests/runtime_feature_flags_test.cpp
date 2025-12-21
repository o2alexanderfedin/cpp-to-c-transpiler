// TDD RED Phase: Tests for modular runtime feature flags
// Story #118: Implement Modular Runtime Feature Flags
//
// This test suite validates command-line flag parsing for runtime features,
// allowing users to enable only the features they need (exceptions, RTTI,
// coroutines, virtual inheritance).

#include <gtest/gtest.h>
#include "RuntimeFeatureFlags.h"
#include <string>
#include <vector>

using namespace clang;

TEST(runtime_feature_flags_test, Parse --runtime=exceptions flag) {
    vector<const char*> args = {"cpptoc", "--runtime=exceptions", "input.cpp"};
        RuntimeFeatureFlags flags(args.size(), args.data());

        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::Exceptions)) << "Exceptions should be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::RTTI)) << "RTTI should NOT be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::Memory)) << "Memory should NOT be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::VInherit)) << "VInherit should NOT be enabled";
}

TEST(runtime_feature_flags_test, Parse --runtime=rtti flag) {
    vector<const char*> args = {"cpptoc", "--runtime=rtti", "input.cpp"};
        RuntimeFeatureFlags flags(args.size(), args.data());

        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::Exceptions)) << "Exceptions should NOT be enabled";
        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::RTTI)) << "RTTI should be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::Memory)) << "Memory should NOT be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::VInherit)) << "VInherit should NOT be enabled";
}

TEST(runtime_feature_flags_test, Parse --runtime=coroutines flag) {
    vector<const char*> args = {"cpptoc", "--runtime=coroutines", "input.cpp"};
        RuntimeFeatureFlags flags(args.size(), args.data());

        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::Exceptions)) << "Exceptions should NOT be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::RTTI)) << "RTTI should NOT be enabled";
        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::Memory)) << "Memory should be enabled for coroutines";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::VInherit)) << "VInherit should NOT be enabled";
}

TEST(runtime_feature_flags_test, Parse --runtime=vinherit flag) {
    vector<const char*> args = {"cpptoc", "--runtime=vinherit", "input.cpp"};
        RuntimeFeatureFlags flags(args.size(), args.data());

        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::Exceptions)) << "Exceptions should NOT be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::RTTI)) << "RTTI should NOT be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::Memory)) << "Memory should NOT be enabled";
        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::VInherit)) << "VInherit should be enabled";
}

TEST(runtime_feature_flags_test, Parse --runtime=exceptions,rtti) {
    vector<const char*> args = {"cpptoc", "--runtime=exceptions,rtti", "input.cpp"};
        RuntimeFeatureFlags flags(args.size(), args.data());

        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::Exceptions)) << "Exceptions should be enabled";
        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::RTTI)) << "RTTI should be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::Memory)) << "Memory should NOT be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::VInherit)) << "VInherit should NOT be enabled";
}

TEST(runtime_feature_flags_test, Parse --runtime=all flag) {
    vector<const char*> args = {"cpptoc", "--runtime=all", "input.cpp"};
        RuntimeFeatureFlags flags(args.size(), args.data());

        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::Exceptions)) << "All features: Exceptions should be enabled";
        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::RTTI)) << "All features: RTTI should be enabled";
        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::Memory)) << "All features: Memory should be enabled";
        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::VInherit)) << "All features: VInherit should be enabled";
}

TEST(runtime_feature_flags_test, Parse --runtime=none flag) {
    vector<const char*> args = {"cpptoc", "--runtime=none", "input.cpp"};
        RuntimeFeatureFlags flags(args.size(), args.data());

        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::Exceptions)) << "None: Exceptions should NOT be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::RTTI)) << "None: RTTI should NOT be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::Memory)) << "None: Memory should NOT be enabled";
        ASSERT_TRUE(!flags.isEnabled(RuntimeFeature::VInherit)) << "None: VInherit should NOT be enabled";
}

TEST(runtime_feature_flags_test, Default behavior (no flag)) {
    ");

        vector<const char*> args = {"cpptoc", "input.cpp"};
        RuntimeFeatureFlags flags(args.size(), args.data());

        // Default: all features enabled (backward compatibility)
        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::Exceptions)) << "Default: Exceptions should be enabled";
        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::RTTI)) << "Default: RTTI should be enabled";
        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::Memory)) << "Default: Memory should be enabled";
        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::VInherit)) << "Default: VInherit should be enabled";");
}

TEST(runtime_feature_flags_test, Get enabled features list) {
    vector<const char*> args = {"cpptoc", "--runtime=exceptions,rtti", "input.cpp"};
        RuntimeFeatureFlags flags(args.size(), args.data());

        auto enabled = flags.getEnabledFeatures();
        ASSERT_TRUE(enabled.size() == 2) << "Should have exactly 2 enabled features";

        bool hasExceptions = false;
        bool hasRTTI = false;
        for (auto feature : enabled) {
            if (feature == RuntimeFeature::Exceptions) hasExceptions = true;
            if (feature == RuntimeFeature::RTTI) hasRTTI = true;
        }
        ASSERT_TRUE(hasExceptions) << "Enabled list should contain Exceptions";
        ASSERT_TRUE(hasRTTI) << "Enabled list should contain RTTI";
}

TEST(runtime_feature_flags_test, Get module size estimates) {
    RuntimeFeatureFlags flags(0, nullptr); // Default constructor

        // Verify size estimates are reasonable
        size_t exceptionSize = flags.getModuleSize(RuntimeFeature::Exceptions);
        size_t rttiSize = flags.getModuleSize(RuntimeFeature::RTTI);
        size_t memorySize = flags.getModuleSize(RuntimeFeature::Memory);
        size_t vinheritSize = flags.getModuleSize(RuntimeFeature::VInherit);

        ASSERT_TRUE(exceptionSize >= 800 && exceptionSize <= 1200) << "Exception module size should be 800-1200 bytes";
        ASSERT_TRUE(rttiSize >= 600 && rttiSize <= 1000) << "RTTI module size should be 600-1000 bytes";
        ASSERT_TRUE(memorySize >= 400 && memorySize <= 800) << "Memory module size should be 400-800 bytes";
        ASSERT_TRUE(vinheritSize >= 500 && vinheritSize <= 900) << "VInherit module size should be 500-900 bytes";
}

TEST(runtime_feature_flags_test, Get total enabled size) {
    vector<const char*> args = {"cpptoc", "--runtime=exceptions,rtti", "input.cpp"};
        RuntimeFeatureFlags flags(args.size(), args.data());

        size_t totalSize = flags.getTotalEnabledSize();

        // Should be sum of exception + RTTI sizes (approx 1400-2200 bytes)
        ASSERT_TRUE(totalSize >= 1400 && totalSize <= 2200) << "Total size should be sum of enabled modules";
}

TEST(runtime_feature_flags_test, Generate preprocessor defines) {
    vector<const char*> args = {"cpptoc", "--runtime=exceptions,rtti", "input.cpp"};
        RuntimeFeatureFlags flags(args.size(), args.data());

        string defines = flags.generatePreprocessorDefines();

        // Should contain #define for enabled features
        ASSERT_TRUE(defines.find("#define CPPTOC_RUNTIME_EXCEPTIONS") != string::npos) << "Should define CPPTOC_RUNTIME_EXCEPTIONS";
        ASSERT_TRUE(defines.find("#define CPPTOC_RUNTIME_RTTI") != string::npos) << "Should define CPPTOC_RUNTIME_RTTI";

        // Should NOT contain defines for disabled features
        ASSERT_TRUE(defines.find("#define CPPTOC_RUNTIME_COROUTINES") == string::npos) << "Should NOT define CPPTOC_RUNTIME_COROUTINES";
        ASSERT_TRUE(defines.find("#define CPPTOC_RUNTIME_VINHERIT") == string::npos) << "Should NOT define CPPTOC_RUNTIME_VINHERIT";
}

TEST(runtime_feature_flags_test, Invalid feature name handling) {
    vector<const char*> args = {"cpptoc", "--runtime=invalid", "input.cpp"};

        try {
            RuntimeFeatureFlags flags(args.size(), args.data());
            TEST_FAIL("Invalid feature name", "Should throw exception for invalid feature");
        } catch (const invalid_argument& e) {
            // Expected behavior
        }
}

TEST(runtime_feature_flags_test, Case-insensitive feature names) {
    vector<const char*> args = {"cpptoc", "--runtime=EXCEPTIONS,Rtti", "input.cpp"};
        RuntimeFeatureFlags flags(args.size(), args.data());

        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::Exceptions)) << "EXCEPTIONS (uppercase;should be enabled");
        ASSERT_TRUE(flags.isEnabled(RuntimeFeature::RTTI)) << "Rtti (mixed case;should be enabled");
}

TEST(runtime_feature_flags_test, Generate size documentation) {
    RuntimeFeatureFlags flags(0, nullptr);

        string sizeDoc = flags.generateSizeDocumentation();

        // Should contain documentation for all modules
        ASSERT_TRUE(sizeDoc.find("exceptions") != string::npos ||
               sizeDoc.find("Exceptions") != string::npos) << "Should document exceptions module";
        ASSERT_TRUE(sizeDoc.find("rtti") != string::npos ||
               sizeDoc.find("RTTI") != string::npos) << "Should document RTTI module";
        ASSERT_TRUE(sizeDoc.find("bytes") != string::npos) << "Should include size in bytes";
}
