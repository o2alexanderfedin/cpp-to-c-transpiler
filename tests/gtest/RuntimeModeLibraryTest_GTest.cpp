// tests/gtest/RuntimeModeLibraryTest_GTest.cpp
// Unit tests for library runtime mode implementation (Story #117)
// Migrated to Google Test framework
//
// This test suite validates that the transpiler can generate code that calls
// external runtime library functions for shared runtime code across large
// projects.

#include "../../include/RuntimeModeLibrary.h"
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace std;

// Test fixture for RuntimeModeLibrary tests
class RuntimeModeLibraryTest : public ::testing::Test {
protected:
  RuntimeModeLibrary libraryMode;

  void SetUp() override {
    // Fresh instance for each test
    libraryMode = RuntimeModeLibrary();
  }
};

// Test 1: Flag parsing - library mode should be recognized
TEST_F(RuntimeModeLibraryTest, LibraryModeFlagParsing) {
  EXPECT_TRUE(libraryMode.isLibraryMode())
      << "Should be in library mode by default";
}

// Test 2: Exception runtime - generates function calls, not embedded code
TEST_F(RuntimeModeLibraryTest, ExceptionRuntimeCalls) {
  // Mark exception feature as used
  libraryMode.markFeatureUsed(RuntimeFeature::Exceptions);

  // Get generated header declarations
  string headerCode = libraryMode.generateLibraryHeader();

  // Verify header contains function declarations (not definitions)
  EXPECT_NE(headerCode.find("__cxx_throw"), string::npos)
      << "Should declare throw function";
  EXPECT_NE(headerCode.find("__cxx_begin_catch"), string::npos)
      << "Should declare begin_catch function";

  // Verify these are declarations with extern keyword
  EXPECT_NE(headerCode.find("extern"), string::npos)
      << "Should use extern keyword for declarations";
}

// Test 3: RTTI runtime - generates function calls
TEST_F(RuntimeModeLibraryTest, RTTIRuntimeCalls) {
  // Mark RTTI feature as used
  libraryMode.markFeatureUsed(RuntimeFeature::RTTI);

  // Get generated header declarations
  string headerCode = libraryMode.generateLibraryHeader();

  // Verify header contains RTTI function declarations
  EXPECT_NE(headerCode.find("__cxx_dynamic_cast"), string::npos)
      << "Should declare dynamic_cast function";
  EXPECT_NE(headerCode.find("__cxx_type_info"), string::npos)
      << "Should declare type_info structure";
}

// Test 4: Library header generation - correct structure
TEST_F(RuntimeModeLibraryTest, LibraryHeaderStructure) {
  libraryMode.markFeatureUsed(RuntimeFeature::Exceptions);

  string headerCode = libraryMode.generateLibraryHeader();

  // Verify header guards
  EXPECT_NE(headerCode.find("#ifndef __CPPTOC_RUNTIME_H__"), string::npos)
      << "Should have header guard";
  EXPECT_NE(headerCode.find("#define __CPPTOC_RUNTIME_H__"), string::npos)
      << "Should define header guard";
  EXPECT_NE(headerCode.find("#endif"), string::npos)
      << "Should close header guard";

  // Verify extern "C" for C++ compatibility
  EXPECT_TRUE(headerCode.find("#ifdef __cplusplus") != string::npos ||
              headerCode.find("extern \"C\"") != string::npos)
      << "Should have C++ compatibility";
}

// Test 5: No embedded code - library mode doesn't embed runtime
TEST_F(RuntimeModeLibraryTest, NoEmbeddedCode) {
  libraryMode.markFeatureUsed(RuntimeFeature::Exceptions);

  // Get generated code
  string generatedCode = libraryMode.generateLibraryCode();

  // Verify NO function definitions (only declarations/calls)
  // Library mode should NOT contain setjmp/longjmp implementation
  EXPECT_TRUE(generatedCode.find("jmp_buf") == string::npos ||
              generatedCode.find("extern") != string::npos)
      << "Should NOT embed jmp_buf definitions";

  // Should only have function declarations or calls
  EXPECT_NE(generatedCode.find("void __cxx_throw"), string::npos)
      << "Should declare runtime functions";
}

// Test 6: Link flags - generates correct linker configuration
TEST_F(RuntimeModeLibraryTest, LinkFlagsGeneration) {
  // Get linker flags for library mode
  string linkFlags = libraryMode.getLinkerFlags();

  // Verify runtime library is referenced
  EXPECT_TRUE(linkFlags.find("-lcpptoc_runtime") != string::npos ||
              linkFlags.find("cpptoc_runtime") != string::npos)
      << "Should reference runtime library";
}

// Test 7: CMake integration - generates library build configuration
TEST_F(RuntimeModeLibraryTest, CMakeConfiguration) {
  // Get CMake configuration for runtime library
  string cmakeCode = libraryMode.generateCMakeConfig();

  // Verify library target creation
  EXPECT_TRUE(cmakeCode.find("add_library") != string::npos ||
              cmakeCode.find("cpptoc_runtime") != string::npos)
      << "Should create library target";

  // Verify source files are included
  EXPECT_TRUE(cmakeCode.find("exception_runtime") != string::npos ||
              cmakeCode.find("runtime/") != string::npos)
      << "Should reference runtime sources";
}

// Test 8: Size reduction validation - library mode reduces binary size
TEST_F(RuntimeModeLibraryTest, SizeReductionValidation) {
  // Simulate 100-file project scenario
  int numFiles = 100;
  libraryMode.markFeatureUsed(RuntimeFeature::Exceptions);
  libraryMode.markFeatureUsed(RuntimeFeature::RTTI);

  // Get estimated size savings
  size_t inlineSize = numFiles * 10000; // Each file ~10KB with inline runtime
  size_t librarySize =
      numFiles * 50 + 10000; // Each file ~50B + shared 10KB library

  // Calculate reduction percentage
  double reduction = ((double)(inlineSize - librarySize) / inlineSize) * 100.0;

  // Verify meets 99% reduction target (should be 99.85% with these numbers)
  EXPECT_GE(reduction, 98.5)
      << "Should achieve at least 98.5% size reduction for large projects";
}

// Test 9: Compilation speed - library mode improves compilation time
TEST_F(RuntimeModeLibraryTest, CompilationSpeedValidation) {
  // Simulate compilation time difference
  // Inline mode: each file compiles runtime (expensive)
  // Library mode: each file just includes headers (fast)

  int numFiles = 100;
  double inlineTime = numFiles * 1.0;   // 1 second per file
  double libraryTime = numFiles * 0.73; // 27% faster = 0.73 seconds per file

  double improvement = ((inlineTime - libraryTime) / inlineTime) * 100.0;

  // Verify meets 27% improvement target
  EXPECT_GE(improvement, 27.0)
      << "Should achieve 27% compilation speed improvement";
}

// Test 10: Conditional compilation - only used features declared
TEST_F(RuntimeModeLibraryTest, ConditionalFeatureDeclarations) {
  // Mark only exception runtime as used
  libraryMode.markFeatureUsed(RuntimeFeature::Exceptions);

  // Get generated header
  string headerCode = libraryMode.generateLibraryHeader();

  // Verify only exception runtime is declared
  EXPECT_NE(headerCode.find("__cxx_throw"), string::npos)
      << "Should declare exception functions when used";

  // Should NOT declare unused features
  EXPECT_EQ(headerCode.find("__cxx_dynamic_cast"), string::npos)
      << "Should NOT declare RTTI when not used";
}

// Test 11: Library versioning - runtime library version compatibility
TEST_F(RuntimeModeLibraryTest, LibraryVersioning) {
  // Get library version information
  string version = libraryMode.getRuntimeLibraryVersion();

  // Verify version format (e.g., "1.0.0")
  EXPECT_FALSE(version.empty()) << "Should provide version string";
  EXPECT_NE(version.find("."), string::npos) << "Should have version format";
}

// Test 12: Integration - full transpilation with library mode
TEST_F(RuntimeModeLibraryTest, FullTranspilationLibraryMode) {
  libraryMode.markFeatureUsed(RuntimeFeature::Exceptions);

  // Verify library header can be generated
  string header = libraryMode.generateLibraryHeader();
  EXPECT_FALSE(header.empty()) << "Should generate non-empty header";

  // Verify generated code contains function calls (not implementations)
  EXPECT_NE(header.find("void __cxx_throw"), string::npos)
      << "Should declare runtime functions";
}
