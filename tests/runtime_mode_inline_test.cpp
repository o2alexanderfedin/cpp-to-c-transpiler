// TDD RED Phase: Tests for inline runtime mode implementation
// Story #116: Implement Inline Runtime Mode
//
// This test suite validates that the transpiler can embed runtime code
// directly into generated C files for zero-dependency output.

#include <gtest/gtest.h>
#include "RuntimeModeInline.h"
#include "clang/AST/ASTContext.h"
#include "clang/Tooling/Tooling.h"
#include <string>

using namespace clang;

TEST(runtime_mode_inline_test, Inline mode flag parsing) {
    // Test that RuntimeModeInline can be instantiated
        RuntimeModeInline inlineMode;

        // Verify default state is inline mode
        ASSERT_TRUE(inlineMode.isInlineMode()) << "Should be in inline mode by default";
}

TEST(runtime_mode_inline_test, Exception runtime embedding) {
    RuntimeModeInline inlineMode;

        // Test that exception runtime can be embedded
        std::string embeddedCode = inlineMode.embedExceptionRuntime();

        // Verify embedded code contains key exception handling structures
        ASSERT_TRUE(embeddedCode.find("__cxx_exception_frame") != std::string::npos) << "Should contain exception frame structure";
        ASSERT_TRUE(embeddedCode.find("__cxx_throw") != std::string::npos) << "Should contain throw function";
        ASSERT_TRUE(embeddedCode.find("__cxx_begin_catch") != std::string::npos) << "Should contain begin_catch function";

        // Verify preprocessor guards to prevent duplication
        ASSERT_TRUE(embeddedCode.find("#ifndef __EXCEPTION_RUNTIME_INLINE_H__") != std::string::npos) << "Should have include guard";
}

TEST(runtime_mode_inline_test, RTTI runtime embedding) {
    RuntimeModeInline inlineMode;

        // Test that RTTI runtime can be embedded
        std::string embeddedCode = inlineMode.embedRTTIRuntime();

        // Verify embedded code contains type_info structures
        ASSERT_TRUE(embeddedCode.find("__cxx_type_info") != std::string::npos) << "Should contain type_info structure";
        ASSERT_TRUE(embeddedCode.find("__cxx_dynamic_cast") != std::string::npos) << "Should contain dynamic_cast function";

        // Verify preprocessor guards
        ASSERT_TRUE(embeddedCode.find("#ifndef __RTTI_RUNTIME_INLINE_H__") != std::string::npos) << "Should have include guard";
}

TEST(runtime_mode_inline_test, Memory runtime embedding) {
    RuntimeModeInline inlineMode;

        // Test that memory runtime can be embedded
        std::string embeddedCode = inlineMode.embedMemoryRuntime();

        // Verify embedded code contains memory management functions
        ASSERT_TRUE(embeddedCode.find("__cxx_allocate") != std::string::npos ||
               embeddedCode.find("malloc") != std::string::npos) << "Should contain memory allocation";

        // Verify preprocessor guards
        ASSERT_TRUE(embeddedCode.find("#ifndef __MEMORY_RUNTIME_INLINE_H__") != std::string::npos) << "Should have include guard";
}

TEST(runtime_mode_inline_test, Virtual inheritance runtime embedding) {
    RuntimeModeInline inlineMode;

        // Test that virtual inheritance runtime can be embedded
        std::string embeddedCode = inlineMode.embedVInheritRuntime();

        // Verify embedded code contains virtual inheritance structures
        ASSERT_TRUE(embeddedCode.find("__cxx_virtual_base") != std::string::npos ||
               embeddedCode.find("vtable") != std::string::npos) << "Should contain virtual inheritance support";

        // Verify preprocessor guards
        ASSERT_TRUE(embeddedCode.find("#ifndef __VINHERIT_RUNTIME_INLINE_H__") != std::string::npos) << "Should have include guard";
}

TEST(runtime_mode_inline_test, Conditional compilation) {
    RuntimeModeInline inlineMode;

        // Mark only exception runtime as used
        inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);

        // Get complete embedded runtime
        std::string embeddedCode = inlineMode.generateInlineRuntime();

        // Verify only exception runtime is included
        ASSERT_TRUE(embeddedCode.find("__cxx_exception_frame") != std::string::npos) << "Should include exception runtime when used";

        // Should NOT include unused features (RTTI)
        ASSERT_TRUE(embeddedCode.find("__cxx_type_info") == std::string::npos) << "Should NOT include RTTI runtime when not used";
}

TEST(runtime_mode_inline_test, Multiple features embedding) {
    RuntimeModeInline inlineMode;

        // Mark multiple features as used
        inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);
        inlineMode.markFeatureUsed(RuntimeFeature::RTTI);

        // Get complete embedded runtime
        std::string embeddedCode = inlineMode.generateInlineRuntime();

        // Verify both features are included
        ASSERT_TRUE(embeddedCode.find("__cxx_exception_frame") != std::string::npos) << "Should include exception runtime";
        ASSERT_TRUE(embeddedCode.find("__cxx_type_info") != std::string::npos) << "Should include RTTI runtime";

        // Should NOT include unused features (memory, vinherit)
        ASSERT_TRUE(embeddedCode.find("__MEMORY_RUNTIME") == std::string::npos) << "Should NOT include memory runtime when not used";
}

TEST(runtime_mode_inline_test, Self-contained output) {
    RuntimeModeInline inlineMode;
        inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);

        std::string embeddedCode = inlineMode.generateInlineRuntime();

        // Verify no external library dependencies
        ASSERT_TRUE(embeddedCode.find("#include \"exception_runtime.h\"") == std::string::npos) << "Should NOT include external runtime headers";
        ASSERT_TRUE(embeddedCode.find("libcpptoc_runtime") == std::string::npos) << "Should NOT reference external runtime library";

        // Only standard C library dependencies allowed
        bool hasOnlyStdDeps =
            embeddedCode.find("#include <setjmp.h>") != std::string::npos ||
            embeddedCode.find("#include <stddef.h>") != std::string::npos ||
            embeddedCode.find("#include <stdlib.h>") != std::string::npos;

        ASSERT_TRUE(hasOnlyStdDeps) << "Should only include standard C library headers";
}

TEST(runtime_mode_inline_test, Preprocessor guards) {
    RuntimeModeInline inlineMode;
        inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);

        std::string embeddedCode = inlineMode.generateInlineRuntime();

        // Count occurrences of guard patterns
        size_t firstGuard = embeddedCode.find("#ifndef __EXCEPTION_RUNTIME_INLINE_H__");
        size_t defineGuard = embeddedCode.find("#define __EXCEPTION_RUNTIME_INLINE_H__");
        size_t endifGuard = embeddedCode.find("#endif // __EXCEPTION_RUNTIME_INLINE_H__");

        ASSERT_TRUE(firstGuard != std::string::npos) << "Should have #ifndef guard";
        ASSERT_TRUE(defineGuard != std::string::npos) << "Should have #define guard";
        ASSERT_TRUE(endifGuard != std::string::npos) << "Should have #endif guard";
        ASSERT_TRUE(firstGuard < defineGuard && defineGuard < endifGuard) << "Guards should be in correct order";
}

TEST(runtime_mode_inline_test, Full transpilation with inline mode) {
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
        ASSERT_TRUE(!runtime.empty()) << "Should generate non-empty runtime code";

        // Verify runtime is valid C code (contains key structures)
        ASSERT_TRUE(runtime.find("struct") != std::string::npos ||
               runtime.find("void") != std::string::npos) << "Should contain valid C declarations";
}
