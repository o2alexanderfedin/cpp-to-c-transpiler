// TDD RED Phase: Tests for modular runtime feature flags
// Story #118: Implement Modular Runtime Feature Flags
//
// This test suite validates command-line flag parsing for runtime features,
// allowing users to enable only the features they need (exceptions, RTTI,
// coroutines, virtual inheritance).

#include "RuntimeFeatureFlags.h"
#include <iostream>
#include <string>
#include <vector>

using namespace std;

// Simple test framework
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) cout << "Running " << name << "... ";
#define TEST_PASS(name) { cout << "✓" << endl; tests_passed++; }
#define TEST_FAIL(name, msg) { cout << "✗ FAILED: " << msg << endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Test 1: Parse single exception flag
void test_parse_exceptions_flag() {
    TEST_START("Parse --runtime=exceptions flag");

    vector<const char*> args = {"cpptoc", "--runtime=exceptions", "input.cpp"};
    RuntimeFeatureFlags flags(args.size(), args.data());

    ASSERT(flags.isEnabled(RuntimeFeature::Exceptions),
           "Exceptions should be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::RTTI),
           "RTTI should NOT be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::Memory),
           "Memory should NOT be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::VInherit),
           "VInherit should NOT be enabled");

    TEST_PASS("Parse --runtime=exceptions flag");
}

// Test 2: Parse single RTTI flag
void test_parse_rtti_flag() {
    TEST_START("Parse --runtime=rtti flag");

    vector<const char*> args = {"cpptoc", "--runtime=rtti", "input.cpp"};
    RuntimeFeatureFlags flags(args.size(), args.data());

    ASSERT(!flags.isEnabled(RuntimeFeature::Exceptions),
           "Exceptions should NOT be enabled");
    ASSERT(flags.isEnabled(RuntimeFeature::RTTI),
           "RTTI should be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::Memory),
           "Memory should NOT be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::VInherit),
           "VInherit should NOT be enabled");

    TEST_PASS("Parse --runtime=rtti flag");
}

// Test 3: Parse single coroutines flag
void test_parse_coroutines_flag() {
    TEST_START("Parse --runtime=coroutines flag");

    vector<const char*> args = {"cpptoc", "--runtime=coroutines", "input.cpp"};
    RuntimeFeatureFlags flags(args.size(), args.data());

    ASSERT(!flags.isEnabled(RuntimeFeature::Exceptions),
           "Exceptions should NOT be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::RTTI),
           "RTTI should NOT be enabled");
    ASSERT(flags.isEnabled(RuntimeFeature::Memory),
           "Memory should be enabled for coroutines");
    ASSERT(!flags.isEnabled(RuntimeFeature::VInherit),
           "VInherit should NOT be enabled");

    TEST_PASS("Parse --runtime=coroutines flag");
}

// Test 4: Parse single vinherit flag
void test_parse_vinherit_flag() {
    TEST_START("Parse --runtime=vinherit flag");

    vector<const char*> args = {"cpptoc", "--runtime=vinherit", "input.cpp"};
    RuntimeFeatureFlags flags(args.size(), args.data());

    ASSERT(!flags.isEnabled(RuntimeFeature::Exceptions),
           "Exceptions should NOT be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::RTTI),
           "RTTI should NOT be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::Memory),
           "Memory should NOT be enabled");
    ASSERT(flags.isEnabled(RuntimeFeature::VInherit),
           "VInherit should be enabled");

    TEST_PASS("Parse --runtime=vinherit flag");
}

// Test 5: Parse multiple features (comma-separated)
void test_parse_multiple_features() {
    TEST_START("Parse --runtime=exceptions,rtti");

    vector<const char*> args = {"cpptoc", "--runtime=exceptions,rtti", "input.cpp"};
    RuntimeFeatureFlags flags(args.size(), args.data());

    ASSERT(flags.isEnabled(RuntimeFeature::Exceptions),
           "Exceptions should be enabled");
    ASSERT(flags.isEnabled(RuntimeFeature::RTTI),
           "RTTI should be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::Memory),
           "Memory should NOT be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::VInherit),
           "VInherit should NOT be enabled");

    TEST_PASS("Parse --runtime=exceptions,rtti");
}

// Test 6: Parse --runtime=all flag
void test_parse_all_flag() {
    TEST_START("Parse --runtime=all flag");

    vector<const char*> args = {"cpptoc", "--runtime=all", "input.cpp"};
    RuntimeFeatureFlags flags(args.size(), args.data());

    ASSERT(flags.isEnabled(RuntimeFeature::Exceptions),
           "All features: Exceptions should be enabled");
    ASSERT(flags.isEnabled(RuntimeFeature::RTTI),
           "All features: RTTI should be enabled");
    ASSERT(flags.isEnabled(RuntimeFeature::Memory),
           "All features: Memory should be enabled");
    ASSERT(flags.isEnabled(RuntimeFeature::VInherit),
           "All features: VInherit should be enabled");

    TEST_PASS("Parse --runtime=all flag");
}

// Test 7: Parse --runtime=none flag
void test_parse_none_flag() {
    TEST_START("Parse --runtime=none flag");

    vector<const char*> args = {"cpptoc", "--runtime=none", "input.cpp"};
    RuntimeFeatureFlags flags(args.size(), args.data());

    ASSERT(!flags.isEnabled(RuntimeFeature::Exceptions),
           "None: Exceptions should NOT be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::RTTI),
           "None: RTTI should NOT be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::Memory),
           "None: Memory should NOT be enabled");
    ASSERT(!flags.isEnabled(RuntimeFeature::VInherit),
           "None: VInherit should NOT be enabled");

    TEST_PASS("Parse --runtime=none flag");
}

// Test 8: Default behavior (no --runtime flag)
void test_default_behavior() {
    TEST_START("Default behavior (no flag)");

    vector<const char*> args = {"cpptoc", "input.cpp"};
    RuntimeFeatureFlags flags(args.size(), args.data());

    // Default: all features enabled (backward compatibility)
    ASSERT(flags.isEnabled(RuntimeFeature::Exceptions),
           "Default: Exceptions should be enabled");
    ASSERT(flags.isEnabled(RuntimeFeature::RTTI),
           "Default: RTTI should be enabled");
    ASSERT(flags.isEnabled(RuntimeFeature::Memory),
           "Default: Memory should be enabled");
    ASSERT(flags.isEnabled(RuntimeFeature::VInherit),
           "Default: VInherit should be enabled");

    TEST_PASS("Default behavior (no flag)");
}

// Test 9: Get enabled features list
void test_get_enabled_features() {
    TEST_START("Get enabled features list");

    vector<const char*> args = {"cpptoc", "--runtime=exceptions,rtti", "input.cpp"};
    RuntimeFeatureFlags flags(args.size(), args.data());

    auto enabled = flags.getEnabledFeatures();
    ASSERT(enabled.size() == 2, "Should have exactly 2 enabled features");

    bool hasExceptions = false;
    bool hasRTTI = false;
    for (auto feature : enabled) {
        if (feature == RuntimeFeature::Exceptions) hasExceptions = true;
        if (feature == RuntimeFeature::RTTI) hasRTTI = true;
    }
    ASSERT(hasExceptions, "Enabled list should contain Exceptions");
    ASSERT(hasRTTI, "Enabled list should contain RTTI");

    TEST_PASS("Get enabled features list");
}

// Test 10: Get module size estimate
void test_get_module_size() {
    TEST_START("Get module size estimates");

    RuntimeFeatureFlags flags(0, nullptr); // Default constructor

    // Verify size estimates are reasonable
    size_t exceptionSize = flags.getModuleSize(RuntimeFeature::Exceptions);
    size_t rttiSize = flags.getModuleSize(RuntimeFeature::RTTI);
    size_t memorySize = flags.getModuleSize(RuntimeFeature::Memory);
    size_t vinheritSize = flags.getModuleSize(RuntimeFeature::VInherit);

    ASSERT(exceptionSize >= 800 && exceptionSize <= 1200,
           "Exception module size should be 800-1200 bytes");
    ASSERT(rttiSize >= 600 && rttiSize <= 1000,
           "RTTI module size should be 600-1000 bytes");
    ASSERT(memorySize >= 400 && memorySize <= 800,
           "Memory module size should be 400-800 bytes");
    ASSERT(vinheritSize >= 500 && vinheritSize <= 900,
           "VInherit module size should be 500-900 bytes");

    TEST_PASS("Get module size estimates");
}

// Test 11: Get total enabled size
void test_get_total_enabled_size() {
    TEST_START("Get total enabled size");

    vector<const char*> args = {"cpptoc", "--runtime=exceptions,rtti", "input.cpp"};
    RuntimeFeatureFlags flags(args.size(), args.data());

    size_t totalSize = flags.getTotalEnabledSize();

    // Should be sum of exception + RTTI sizes (approx 1400-2200 bytes)
    ASSERT(totalSize >= 1400 && totalSize <= 2200,
           "Total size should be sum of enabled modules");

    TEST_PASS("Get total enabled size");
}

// Test 12: Generate preprocessor defines
void test_generate_preprocessor_defines() {
    TEST_START("Generate preprocessor defines");

    vector<const char*> args = {"cpptoc", "--runtime=exceptions,rtti", "input.cpp"};
    RuntimeFeatureFlags flags(args.size(), args.data());

    string defines = flags.generatePreprocessorDefines();

    // Should contain #define for enabled features
    ASSERT(defines.find("#define CPPTOC_RUNTIME_EXCEPTIONS") != string::npos,
           "Should define CPPTOC_RUNTIME_EXCEPTIONS");
    ASSERT(defines.find("#define CPPTOC_RUNTIME_RTTI") != string::npos,
           "Should define CPPTOC_RUNTIME_RTTI");

    // Should NOT contain defines for disabled features
    ASSERT(defines.find("#define CPPTOC_RUNTIME_COROUTINES") == string::npos,
           "Should NOT define CPPTOC_RUNTIME_COROUTINES");
    ASSERT(defines.find("#define CPPTOC_RUNTIME_VINHERIT") == string::npos,
           "Should NOT define CPPTOC_RUNTIME_VINHERIT");

    TEST_PASS("Generate preprocessor defines");
}

// Test 13: Invalid feature name handling
void test_invalid_feature_name() {
    TEST_START("Invalid feature name handling");

    vector<const char*> args = {"cpptoc", "--runtime=invalid", "input.cpp"};

    try {
        RuntimeFeatureFlags flags(args.size(), args.data());
        TEST_FAIL("Invalid feature name", "Should throw exception for invalid feature");
    } catch (const invalid_argument& e) {
        // Expected behavior
        TEST_PASS("Invalid feature name handling");
    }
}

// Test 14: Case-insensitive feature names
void test_case_insensitive_names() {
    TEST_START("Case-insensitive feature names");

    vector<const char*> args = {"cpptoc", "--runtime=EXCEPTIONS,Rtti", "input.cpp"};
    RuntimeFeatureFlags flags(args.size(), args.data());

    ASSERT(flags.isEnabled(RuntimeFeature::Exceptions),
           "EXCEPTIONS (uppercase) should be enabled");
    ASSERT(flags.isEnabled(RuntimeFeature::RTTI),
           "Rtti (mixed case) should be enabled");

    TEST_PASS("Case-insensitive feature names");
}

// Test 15: Module size documentation
void test_generate_size_documentation() {
    TEST_START("Generate size documentation");

    RuntimeFeatureFlags flags(0, nullptr);

    string sizeDoc = flags.generateSizeDocumentation();

    // Should contain documentation for all modules
    ASSERT(sizeDoc.find("exceptions") != string::npos ||
           sizeDoc.find("Exceptions") != string::npos,
           "Should document exceptions module");
    ASSERT(sizeDoc.find("rtti") != string::npos ||
           sizeDoc.find("RTTI") != string::npos,
           "Should document RTTI module");
    ASSERT(sizeDoc.find("bytes") != string::npos,
           "Should include size in bytes");

    TEST_PASS("Generate size documentation");
}

int main() {
    cout << "=== Runtime Feature Flags Tests (TDD RED Phase) ===" << endl;
    cout << endl;

    // Run all tests
    test_parse_exceptions_flag();
    test_parse_rtti_flag();
    test_parse_coroutines_flag();
    test_parse_vinherit_flag();
    test_parse_multiple_features();
    test_parse_all_flag();
    test_parse_none_flag();
    test_default_behavior();
    test_get_enabled_features();
    test_get_module_size();
    test_get_total_enabled_size();
    test_generate_preprocessor_defines();
    test_invalid_feature_name();
    test_case_insensitive_names();
    test_generate_size_documentation();

    // Summary
    cout << endl;
    cout << "=== Test Summary ===" << endl;
    cout << "Passed: " << tests_passed << endl;
    cout << "Failed: " << tests_failed << endl;

    return tests_failed > 0 ? 1 : 0;
}
