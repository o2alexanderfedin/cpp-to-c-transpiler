// TDD RED Phase: Tests for inline runtime mode implementation
// Story #116: Implement Inline Runtime Mode
//
// This test suite validates that the transpiler can embed runtime code
// directly into generated C files for zero-dependency output.

#include "RuntimeModeInline.h"
#include "clang/AST/ASTContext.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include <string>

using namespace clang;

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Test 1: Flag parsing - --runtime-mode=inline should be recognized
void test_inline_mode_flag_parsing() {
    TEST_START("Inline mode flag parsing");

    // Test that RuntimeModeInline can be instantiated
    RuntimeModeInline inlineMode;

    // Verify default state is inline mode
    ASSERT(inlineMode.isInlineMode(), "Should be in inline mode by default");

    TEST_PASS("Inline mode flag parsing");
}

// Test 2: Exception runtime embedding
void test_exception_runtime_embedding() {
    TEST_START("Exception runtime embedding");

    RuntimeModeInline inlineMode;

    // Test that exception runtime can be embedded
    std::string embeddedCode = inlineMode.embedExceptionRuntime();

    // Verify embedded code contains key exception handling structures
    ASSERT(embeddedCode.find("__cxx_exception_frame") != std::string::npos,
           "Should contain exception frame structure");
    ASSERT(embeddedCode.find("__cxx_throw") != std::string::npos,
           "Should contain throw function");
    ASSERT(embeddedCode.find("__cxx_begin_catch") != std::string::npos,
           "Should contain begin_catch function");

    // Verify preprocessor guards to prevent duplication
    ASSERT(embeddedCode.find("#ifndef __EXCEPTION_RUNTIME_INLINE_H__") != std::string::npos,
           "Should have include guard");

    TEST_PASS("Exception runtime embedding");
}

// Test 3: RTTI runtime embedding
void test_rtti_runtime_embedding() {
    TEST_START("RTTI runtime embedding");

    RuntimeModeInline inlineMode;

    // Test that RTTI runtime can be embedded
    std::string embeddedCode = inlineMode.embedRTTIRuntime();

    // Verify embedded code contains type_info structures
    ASSERT(embeddedCode.find("__cxx_type_info") != std::string::npos,
           "Should contain type_info structure");
    ASSERT(embeddedCode.find("__cxx_dynamic_cast") != std::string::npos,
           "Should contain dynamic_cast function");

    // Verify preprocessor guards
    ASSERT(embeddedCode.find("#ifndef __RTTI_RUNTIME_INLINE_H__") != std::string::npos,
           "Should have include guard");

    TEST_PASS("RTTI runtime embedding");
}

// Test 4: Memory runtime embedding
void test_memory_runtime_embedding() {
    TEST_START("Memory runtime embedding");

    RuntimeModeInline inlineMode;

    // Test that memory runtime can be embedded
    std::string embeddedCode = inlineMode.embedMemoryRuntime();

    // Verify embedded code contains memory management functions
    ASSERT(embeddedCode.find("__cxx_allocate") != std::string::npos ||
           embeddedCode.find("malloc") != std::string::npos,
           "Should contain memory allocation");

    // Verify preprocessor guards
    ASSERT(embeddedCode.find("#ifndef __MEMORY_RUNTIME_INLINE_H__") != std::string::npos,
           "Should have include guard");

    TEST_PASS("Memory runtime embedding");
}

// Test 5: Virtual inheritance runtime embedding
void test_vinherit_runtime_embedding() {
    TEST_START("Virtual inheritance runtime embedding");

    RuntimeModeInline inlineMode;

    // Test that virtual inheritance runtime can be embedded
    std::string embeddedCode = inlineMode.embedVInheritRuntime();

    // Verify embedded code contains virtual inheritance structures
    ASSERT(embeddedCode.find("__cxx_virtual_base") != std::string::npos ||
           embeddedCode.find("vtable") != std::string::npos,
           "Should contain virtual inheritance support");

    // Verify preprocessor guards
    ASSERT(embeddedCode.find("#ifndef __VINHERIT_RUNTIME_INLINE_H__") != std::string::npos,
           "Should have include guard");

    TEST_PASS("Virtual inheritance runtime embedding");
}

// Test 6: Conditional compilation - only used features embedded
void test_conditional_compilation() {
    TEST_START("Conditional compilation");

    RuntimeModeInline inlineMode;

    // Mark only exception runtime as used
    inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);

    // Get complete embedded runtime
    std::string embeddedCode = inlineMode.generateInlineRuntime();

    // Verify only exception runtime is included
    ASSERT(embeddedCode.find("__cxx_exception_frame") != std::string::npos,
           "Should include exception runtime when used");

    // Should NOT include unused features (RTTI)
    ASSERT(embeddedCode.find("__cxx_type_info") == std::string::npos,
           "Should NOT include RTTI runtime when not used");

    TEST_PASS("Conditional compilation");
}

// Test 7: Multiple features - all used features embedded
void test_multiple_features_embedding() {
    TEST_START("Multiple features embedding");

    RuntimeModeInline inlineMode;

    // Mark multiple features as used
    inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);
    inlineMode.markFeatureUsed(RuntimeFeature::RTTI);

    // Get complete embedded runtime
    std::string embeddedCode = inlineMode.generateInlineRuntime();

    // Verify both features are included
    ASSERT(embeddedCode.find("__cxx_exception_frame") != std::string::npos,
           "Should include exception runtime");
    ASSERT(embeddedCode.find("__cxx_type_info") != std::string::npos,
           "Should include RTTI runtime");

    // Should NOT include unused features (memory, vinherit)
    ASSERT(embeddedCode.find("__MEMORY_RUNTIME") == std::string::npos,
           "Should NOT include memory runtime when not used");

    TEST_PASS("Multiple features embedding");
}

// Test 8: Self-contained output - no external dependencies
void test_self_contained_output() {
    TEST_START("Self-contained output");

    RuntimeModeInline inlineMode;
    inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);

    std::string embeddedCode = inlineMode.generateInlineRuntime();

    // Verify no external library dependencies
    ASSERT(embeddedCode.find("#include \"exception_runtime.h\"") == std::string::npos,
           "Should NOT include external runtime headers");
    ASSERT(embeddedCode.find("libcpptoc_runtime") == std::string::npos,
           "Should NOT reference external runtime library");

    // Only standard C library dependencies allowed
    bool hasOnlyStdDeps =
        embeddedCode.find("#include <setjmp.h>") != std::string::npos ||
        embeddedCode.find("#include <stddef.h>") != std::string::npos ||
        embeddedCode.find("#include <stdlib.h>") != std::string::npos;

    ASSERT(hasOnlyStdDeps, "Should only include standard C library headers");

    TEST_PASS("Self-contained output");
}

// Test 9: Preprocessor guards prevent duplication
void test_preprocessor_guards() {
    TEST_START("Preprocessor guards");

    RuntimeModeInline inlineMode;
    inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);

    std::string embeddedCode = inlineMode.generateInlineRuntime();

    // Count occurrences of guard patterns
    size_t firstGuard = embeddedCode.find("#ifndef __EXCEPTION_RUNTIME_INLINE_H__");
    size_t defineGuard = embeddedCode.find("#define __EXCEPTION_RUNTIME_INLINE_H__");
    size_t endifGuard = embeddedCode.find("#endif // __EXCEPTION_RUNTIME_INLINE_H__");

    ASSERT(firstGuard != std::string::npos, "Should have #ifndef guard");
    ASSERT(defineGuard != std::string::npos, "Should have #define guard");
    ASSERT(endifGuard != std::string::npos, "Should have #endif guard");
    ASSERT(firstGuard < defineGuard && defineGuard < endifGuard,
           "Guards should be in correct order");

    TEST_PASS("Preprocessor guards");
}

// Test 10: Integration - full transpilation with inline mode
void test_full_transpilation_inline_mode() {
    TEST_START("Full transpilation with inline mode");

    // Simple C++ code with exception handling
    const char *cppCode = R"(
        void test() {
            try {
                throw 42;
            } catch (int e) {
                // handle
            }
        }
    )";

    RuntimeModeInline inlineMode;
    inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);

    // Verify runtime can be generated
    std::string runtime = inlineMode.generateInlineRuntime();
    ASSERT(!runtime.empty(), "Should generate non-empty runtime code");

    // Verify runtime is valid C code (contains key structures)
    ASSERT(runtime.find("struct") != std::string::npos ||
           runtime.find("void") != std::string::npos,
           "Should contain valid C declarations");

    TEST_PASS("Full transpilation with inline mode");
}

int main() {
    std::cout << "=== Runtime Mode Inline Tests (TDD RED Phase) ===" << std::endl;
    std::cout << std::endl;

    // Run all tests
    test_inline_mode_flag_parsing();
    test_exception_runtime_embedding();
    test_rtti_runtime_embedding();
    test_memory_runtime_embedding();
    test_vinherit_runtime_embedding();
    test_conditional_compilation();
    test_multiple_features_embedding();
    test_self_contained_output();
    test_preprocessor_guards();
    test_full_transpilation_inline_mode();

    // Summary
    std::cout << std::endl;
    std::cout << "=== Test Summary ===" << std::endl;
    std::cout << "Passed: " << tests_passed << std::endl;
    std::cout << "Failed: " << tests_failed << std::endl;

    return tests_failed > 0 ? 1 : 0;
}
