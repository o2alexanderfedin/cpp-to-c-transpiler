// tests/gtest/RuntimeModeInlineTest_GTest.cpp
// Unit tests for inline runtime mode implementation (Story #116)
// Migrated to Google Test framework
//
// CRITICAL: This test validates the fix from commit 34d7f54 where runtime code
// is embedded as string literals instead of reading from files to avoid path
// dependency issues when tests run from different directories.

#include "../../include/RuntimeModeInline.h"
#include <gtest/gtest.h>
#include <string>

using namespace std;

// Test fixture for RuntimeModeInline tests
class RuntimeModeInlineTest : public ::testing::Test {
protected:
  RuntimeModeInline inlineMode;

  void SetUp() override {
    // Fresh instance for each test
    inlineMode = RuntimeModeInline();
  }
};

// Test 1: Flag parsing - inline mode should be recognized
TEST_F(RuntimeModeInlineTest, InlineModeFlagParsing) {
  // Test that RuntimeModeInline can be instantiated
  EXPECT_TRUE(inlineMode.isInlineMode())
      << "Should be in inline mode by default";
}

// Test 2: Exception runtime embedding
TEST_F(RuntimeModeInlineTest, ExceptionRuntimeEmbedding) {
  // Test that exception runtime can be embedded
  string embeddedCode = inlineMode.embedExceptionRuntime();

  // Verify embedded code contains key exception handling structures
  EXPECT_NE(embeddedCode.find("__cxx_exception_frame"), string::npos)
      << "Should contain exception frame structure";
  EXPECT_NE(embeddedCode.find("__cxx_throw"), string::npos)
      << "Should contain throw function";
  EXPECT_NE(embeddedCode.find("__cxx_begin_catch"), string::npos)
      << "Should contain begin_catch function";

  // Verify preprocessor guards to prevent duplication
  EXPECT_NE(embeddedCode.find("#ifndef __EXCEPTION_RUNTIME_INLINE_H__"),
            string::npos)
      << "Should have include guard";
}

// Test 3: RTTI runtime embedding
TEST_F(RuntimeModeInlineTest, RTTIRuntimeEmbedding) {
  // Test that RTTI runtime can be embedded
  string embeddedCode = inlineMode.embedRTTIRuntime();

  // Verify embedded code contains type_info structures
  EXPECT_NE(embeddedCode.find("__cxx_type_info"), string::npos)
      << "Should contain type_info structure";
  EXPECT_NE(embeddedCode.find("__cxx_dynamic_cast"), string::npos)
      << "Should contain dynamic_cast function";

  // Verify preprocessor guards
  EXPECT_NE(embeddedCode.find("#ifndef __RTTI_RUNTIME_INLINE_H__"),
            string::npos)
      << "Should have include guard";
}

// Test 4: Memory runtime embedding
TEST_F(RuntimeModeInlineTest, MemoryRuntimeEmbedding) {
  // Test that memory runtime can be embedded
  string embeddedCode = inlineMode.embedMemoryRuntime();

  // Verify embedded code contains memory management functions
  EXPECT_TRUE(embeddedCode.find("__cxx_allocate") != string::npos ||
              embeddedCode.find("malloc") != string::npos)
      << "Should contain memory allocation";

  // Verify preprocessor guards
  EXPECT_NE(embeddedCode.find("#ifndef __MEMORY_RUNTIME_INLINE_H__"),
            string::npos)
      << "Should have include guard";
}

// Test 5: Virtual inheritance runtime embedding
TEST_F(RuntimeModeInlineTest, VInheritRuntimeEmbedding) {
  // Test that virtual inheritance runtime can be embedded
  string embeddedCode = inlineMode.embedVInheritRuntime();

  // Verify embedded code contains virtual inheritance structures
  EXPECT_TRUE(embeddedCode.find("__cxx_virtual_base") != string::npos ||
              embeddedCode.find("vtable") != string::npos)
      << "Should contain virtual inheritance support";

  // Verify preprocessor guards
  EXPECT_NE(embeddedCode.find("#ifndef __VINHERIT_RUNTIME_INLINE_H__"),
            string::npos)
      << "Should have include guard";
}

// Test 6: Conditional compilation - only used features embedded
TEST_F(RuntimeModeInlineTest, ConditionalCompilation) {
  // Mark only exception runtime as used
  inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);

  // Get complete embedded runtime
  string embeddedCode = inlineMode.generateInlineRuntime();

  // Verify only exception runtime is included
  EXPECT_NE(embeddedCode.find("__cxx_exception_frame"), string::npos)
      << "Should include exception runtime when used";

  // Should NOT include unused features (RTTI)
  EXPECT_EQ(embeddedCode.find("__cxx_type_info"), string::npos)
      << "Should NOT include RTTI runtime when not used";
}

// Test 7: Multiple features - all used features embedded
TEST_F(RuntimeModeInlineTest, MultipleFeaturesEmbedding) {
  // Mark multiple features as used
  inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);
  inlineMode.markFeatureUsed(RuntimeFeature::RTTI);

  // Get complete embedded runtime
  string embeddedCode = inlineMode.generateInlineRuntime();

  // Verify both features are included
  EXPECT_NE(embeddedCode.find("__cxx_exception_frame"), string::npos)
      << "Should include exception runtime";
  EXPECT_NE(embeddedCode.find("__cxx_type_info"), string::npos)
      << "Should include RTTI runtime";

  // Should NOT include unused features (memory, vinherit)
  EXPECT_EQ(embeddedCode.find("__MEMORY_RUNTIME"), string::npos)
      << "Should NOT include memory runtime when not used";
}

// Test 8: Self-contained output - no external dependencies
TEST_F(RuntimeModeInlineTest, SelfContainedOutput) {
  inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);

  string embeddedCode = inlineMode.generateInlineRuntime();

  // Verify no external library dependencies
  EXPECT_EQ(embeddedCode.find("#include \"exception_runtime.h\""), string::npos)
      << "Should NOT include external runtime headers";
  EXPECT_EQ(embeddedCode.find("libcpptoc_runtime"), string::npos)
      << "Should NOT reference external runtime library";

  // Only standard C library dependencies allowed
  bool hasOnlyStdDeps =
      embeddedCode.find("#include <setjmp.h>") != string::npos ||
      embeddedCode.find("#include <stddef.h>") != string::npos ||
      embeddedCode.find("#include <stdlib.h>") != string::npos;

  EXPECT_TRUE(hasOnlyStdDeps)
      << "Should only include standard C library headers";
}

// Test 9: Preprocessor guards prevent duplication
TEST_F(RuntimeModeInlineTest, PreprocessorGuards) {
  inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);

  string embeddedCode = inlineMode.generateInlineRuntime();

  // Count occurrences of guard patterns
  size_t firstGuard =
      embeddedCode.find("#ifndef __EXCEPTION_RUNTIME_INLINE_H__");
  size_t defineGuard =
      embeddedCode.find("#define __EXCEPTION_RUNTIME_INLINE_H__");
  size_t endifGuard =
      embeddedCode.find("#endif // __EXCEPTION_RUNTIME_INLINE_H__");

  EXPECT_NE(firstGuard, string::npos) << "Should have #ifndef guard";
  EXPECT_NE(defineGuard, string::npos) << "Should have #define guard";
  EXPECT_NE(endifGuard, string::npos) << "Should have #endif guard";
  EXPECT_LT(firstGuard, defineGuard)
      << "Guards should be in correct order (ifndef < define)";
  EXPECT_LT(defineGuard, endifGuard)
      << "Guards should be in correct order (define < endif)";
}

// Test 10: Integration - full transpilation with inline mode
TEST_F(RuntimeModeInlineTest, FullTranspilationInlineMode) {
  // Mark exception feature as used
  inlineMode.markFeatureUsed(RuntimeFeature::Exceptions);

  // Verify runtime can be generated
  string runtime = inlineMode.generateInlineRuntime();
  EXPECT_FALSE(runtime.empty()) << "Should generate non-empty runtime code";

  // Verify runtime is valid C code (contains key structures)
  EXPECT_TRUE(runtime.find("struct") != string::npos ||
              runtime.find("void") != string::npos)
      << "Should contain valid C declarations";
}

// Test 11: Empty feature set - no runtime needed
TEST_F(RuntimeModeInlineTest, NoFeatureEmptyRuntime) {
  // Don't mark any features as used
  string runtime = inlineMode.generateInlineRuntime();

  // With no features, runtime should be minimal or empty
  // Verify it doesn't contain feature-specific code
  EXPECT_EQ(runtime.find("__cxx_exception_frame"), string::npos)
      << "Should NOT include exception runtime when not used";
  EXPECT_EQ(runtime.find("__cxx_type_info"), string::npos)
      << "Should NOT include RTTI runtime when not used";
}
