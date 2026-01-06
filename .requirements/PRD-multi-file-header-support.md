# Product Requirements Document: Multi-File Input and Header Directory Support

**Version:** 1.0
**Date:** 2025-12-23
**Status:** Draft
**Author:** Requirements Gathering Interview

---

## Executive Summary

Enhance the C++ to C transpiler to support clang-like command-line interface for multiple input files and header include directories. The current CLI already supports multiple files, but the Library API (TranspilerAPI) processes one file at a time. The critical missing feature is support for include directories (`-I` flag), which prevents standard C++ include syntax and makes header management difficult.

---

## Table of Contents

1. [Problem Statement](#problem-statement)
2. [Current State Analysis](#current-state-analysis)
3. [Requirements](#requirements)
4. [Success Criteria](#success-criteria)
5. [Technical Architecture](#technical-architecture)
6. [Implementation Plan](#implementation-plan)
7. [Testing Strategy](#testing-strategy)
8. [Risk Assessment](#risk-assessment)
9. [Appendices](#appendices)

---

## 1. Problem Statement

### 1.1 User Pain Points

**Primary Issue:**
- Cannot use standard C++ include syntax like `#include <header.h>` or `#include "myheader.h"`
- Must use absolute paths: `#include "/virtual/stdio.h"` (awkward and non-standard)
- No support for multiple include directories (like clang's `-I/path1 -I/path2`)

**Secondary Issues:**
- Library API (TranspilerAPI) only processes single source string at a time
- Difficult to integrate standard library headers
- WASM/browser usage requires verbose absolute path specifications

### 1.2 Business Impact

- **Developer Experience**: Poor UX compared to standard compilers
- **Adoption**: Barrier for users familiar with clang/gcc workflows
- **Integration**: Difficult to integrate with existing build systems
- **WASM Usage**: Makes browser-based transpilation awkward

### 1.3 Stakeholders

- **Primary**: Developers using cpptoc transpiler
- **Secondary**:
  - WASM/browser users
  - Build system integrators
  - Standard library users
  - Safety-critical system developers (Frama-C users)

---

## 2. Current State Analysis

### 2.1 What Works ✅

#### CLI Multi-File Support (Already Implemented)
- **Status**: ✅ WORKING
- **Implementation**: Uses `CommonOptionsParser` correctly
- **Usage**: `cpptoc file1.cpp file2.cpp file3.cpp --`
- **Code**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/main.cpp:185-191`

```cpp
ClangTool Tool(OptionsParser.getCompilations(),
               OptionsParser.getSourcePathList());  // Gets list of files
```

#### Virtual File System (VFS)
- **Status**: ✅ COMPLETE (Phase 27-01)
- **Functionality**: In-memory header files for WASM/browser usage
- **Code**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/TranspilerAPI.cpp:257-272`
- **Tests**: 8 comprehensive tests passing

```cpp
struct TranspileOptions {
    std::vector<std::pair<std::string, std::string>> virtualFiles;
};
```

#### Header/Implementation Separation
- **Status**: ✅ COMPLETE (Phase 28)
- **Components**: `HeaderSeparator`, `IncludeGuardGenerator`
- **Functionality**: Automatically splits code into `.h` and `.c` files

### 2.2 What's Missing ❌

#### Include Directory Support
- **Status**: ❌ NOT IMPLEMENTED
- **Critical Gap**: No support for `-I` flags
- **Impact**: Cannot use standard include syntax
- **Planned**: Phase 27-02 (implementation plan exists)

**Example of what doesn't work:**
```bash
# This doesn't work (include paths not supported)
cpptoc main.cpp -- -I./include -I./third_party

# Must use absolute paths instead (awkward)
opts.virtualFiles = {{"/absolute/path/header.h", content}};
```

#### Library API Multi-File Support
- **Status**: ❌ SINGLE FILE ONLY
- **Current**: `transpile(string cppSource, ...)` accepts one source string
- **Limitation**: Cannot transpile multiple physical files in one API call
- **Workaround**: Use VFS for headers, but not for multiple source files

### 2.3 Existing Infrastructure to Build Upon

#### Compiler Arguments Infrastructure
- **Location**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/TranspilerAPI.cpp:230-246`
- **Ready to extend**: Easy to add `-I` flag support (3 lines of code)

```cpp
std::vector<std::string> args;
args.push_back("-std=c++" + std::to_string(options.cppStandard));
// Easy to add here:
// for (const auto& path : options.includePaths) {
//     args.push_back("-I" + path);
// }
```

#### Test Infrastructure
- Comprehensive test suites for VFS
- Header separation tests
- Runtime test harness
- Integration test framework

---

## 3. Requirements

### 3.1 Functional Requirements

#### FR-1: Include Directory Support (CRITICAL)

**Priority:** P0 (Critical)
**Status:** Not Implemented

**Description:**
Support clang-like include directory syntax via `-I` flag to enable standard C++ include patterns.

**User Story:**
> As a developer using cpptoc, I want to specify header directories with `-I` flags, so I can use standard C++ include syntax like `#include <header.h>` instead of absolute paths.

**Acceptance Criteria:**
1. ✅ CLI accepts `-I<directory>` flags after `--` separator
2. ✅ Multiple `-I` flags are supported (processed in order)
3. ✅ Include paths are relative to working directory
4. ✅ Standard include syntax works: `#include <header.h>`, `#include "header.h"`
5. ✅ Include path search order matches clang behavior
6. ✅ Library API supports `includePaths` option in `TranspileOptions`

**Examples:**
```bash
# CLI usage
cpptoc main.cpp -- -I./include -I./third_party -std=c++20

# API usage
cpptoc::TranspileOptions opts;
opts.includePaths = {"./include", "./third_party"};
auto result = cpptoc::transpile(cppSource, "main.cpp", opts);
```

**Technical Notes:**
- Include paths passed to Clang as `-I` flags
- Search order: specified paths → system paths
- Paths resolved relative to compilation working directory
- Implementation in Phase 27-02 (plan exists)

---

#### FR-2: Maintain Multi-File CLI Support (Already Works)

**Priority:** P1 (High)
**Status:** ✅ Implemented

**Description:**
Continue supporting multiple input files via CLI (already working, ensure not broken).

**Acceptance Criteria:**
1. ✅ CLI accepts multiple source files as positional arguments
2. ✅ Files processed independently (separate AST per file)
3. ✅ Each file generates separate `.c` and `.h` output
4. ✅ Per-file error reporting

**Current Usage:**
```bash
cpptoc file1.cpp file2.cpp file3.cpp -- -std=c++20
```

---

#### FR-3: Library API Enhancement (Optional)

**Priority:** P2 (Medium)
**Status:** Not Required (Future Enhancement)

**Description:**
Optionally enhance Library API to accept multiple source files in one call.

**Rationale:**
- Current single-file API is sufficient for most use cases
- VFS provides header support
- Multi-file API can be added later without breaking changes

**Acceptance Criteria (Future):**
1. New API: `transpileMultiple(vector<SourceFile>, TranspileOptions)`
2. Returns: `vector<TranspileResult>` (one per source file)
3. Backward compatible with existing `transpile()` API

---

### 3.2 Non-Functional Requirements

#### NFR-1: Performance
- Include path resolution should add < 1ms overhead per file
- Virtual file lookup should remain O(1) or O(log n)
- No performance regression for existing single-file usage

#### NFR-2: Compatibility
- **Backward Compatible**: Existing API unchanged (additive changes only)
- **Clang Compatible**: Follow clang's include path behavior exactly
- **Build System Compatible**: Work with CMake, Make, compilation databases

#### NFR-3: Usability
- **Familiar Syntax**: Match clang/gcc command-line conventions
- **Clear Errors**: Helpful messages when include paths don't exist
- **Documentation**: Update all docs with new flag usage

#### NFR-4: Testability
- **Unit Tests**: 5+ tests for include path feature
- **Integration Tests**: Multi-file + include path scenarios
- **Regression Tests**: Ensure existing tests still pass

---

### 3.3 Out of Scope (Not Required)

The following are explicitly **not required** for this iteration:

1. ❌ **Compilation Database Support**: Already works via CommonOptionsParser
2. ❌ **Cross-File Dependency Analysis**: Each file transpiled independently
3. ❌ **Multi-File Library API**: Deferred to future enhancement
4. ❌ **Include Path Validation**: Clang handles this (graceful errors)
5. ❌ **Recursive Include Directory Search**: Standard clang behavior only
6. ❌ **Response File Support**: Can be added later if needed

---

## 4. Success Criteria

### 4.1 Must Have (Minimum Viable Feature)

1. ✅ Include directory support via `-I` flag (CLI)
2. ✅ Include directory support via `includePaths` option (API)
3. ✅ Standard include syntax works: `#include <header.h>`
4. ✅ Multiple `-I` flags supported (correct search order)
5. ✅ 5+ unit tests passing for include path feature
6. ✅ All existing tests still pass (no regression)
7. ✅ Documentation updated (README, API docs)

### 4.2 Should Have (Desired Features)

1. Include path validation warning (if directory doesn't exist)
2. Verbose mode showing include path search order
3. Integration tests combining multi-file + include paths
4. Examples in documentation showing real-world usage

### 4.3 Nice to Have (Future Enhancements)

1. Multi-file Library API (`transpileMultiple()`)
2. Compilation database generation helper
3. Response file support for long argument lists
4. Include dependency graph visualization

---

## 5. Technical Architecture

### 5.1 High-Level Design

```
User Input (CLI or API)
    ↓
Include Paths Option
    ↓
Convert to Clang -I flags
    ↓
Pass to runToolOnCodeWithArgs()
    ↓
Clang resolves includes via paths
    ↓
AST includes resolved headers
    ↓
Transpile as normal
```

### 5.2 Component Changes

#### A. TranspilerAPI.h (API Change)

**Location:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/TranspilerAPI.h:75-80`

**Change:**
```cpp
struct TranspileOptions {
    // Existing fields...
    std::vector<std::pair<std::string, std::string>> virtualFiles;

    // NEW: Include directories
    /// @brief Include directories for header file search
    /// @details Directories are searched in order (like -I flags).
    ///          Paths are relative to working directory.
    std::vector<std::string> includePaths;
};
```

**Impact:**
- Additive change (backward compatible)
- No breaking changes to existing API users

#### B. TranspilerAPI.cpp (Implementation)

**Location:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/TranspilerAPI.cpp:230-246`

**Change:**
```cpp
std::vector<std::string> args;
args.push_back("-std=c++" + std::to_string(options.cppStandard));
args.push_back("-fsyntax-only");

// NEW: Add include paths
for (const auto& includePath : options.includePaths) {
    args.push_back("-I" + includePath);
}

// ... rest of args
```

**Impact:**
- 3 lines of code added
- Minimal complexity
- Low risk

#### C. CLI (No Changes Required)

**Location:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/main.cpp`

**Status:** Already supports `-I` flags via `--` separator

**Usage:**
```bash
cpptoc main.cpp -- -I./include -I./third_party
```

**Rationale:**
- CommonOptionsParser automatically passes flags to Clang
- No code changes needed for CLI
- Just need documentation updates

### 5.3 Data Flow

#### CLI Flow
```
User: cpptoc main.cpp -- -I./include
    ↓
CommonOptionsParser extracts: files=[main.cpp], flags=[-I./include]
    ↓
ClangTool runs with compilation database (includes -I flags)
    ↓
Clang resolves: #include <header.h> → ./include/header.h
    ↓
AST built with resolved headers
    ↓
Transpile to C code
```

#### API Flow
```
User: opts.includePaths = {"./include"}
      transpile(source, "main.cpp", opts)
    ↓
Build args: ["-std=c++20", "-I./include", ...]
    ↓
runToolOnCodeWithArgs(source, args, ...)
    ↓
Clang resolves: #include <header.h> → ./include/header.h
    ↓
AST built with resolved headers
    ↓
Transpile to C code
```

### 5.4 Integration Points

#### With Virtual File System
```cpp
// Include paths and VFS work together
opts.includePaths = {"./include"};
opts.virtualFiles = {{"/virtual/extra.h", content}};

// Clang searches:
// 1. ./include/ (physical filesystem)
// 2. /virtual/ (VFS)
// 3. System paths
```

#### With Header Separation
```
Input files with includes
    ↓
Resolve via include paths
    ↓
Build full AST
    ↓
HeaderSeparator splits into .h and .c
    ↓
Generated .c includes generated .h
```

---

## 6. Implementation Plan

### 6.1 Phase 1: Include Path Support (Phase 27-02)

**Estimated Effort:** 1-2 hours
**Risk:** Low
**Priority:** P0 (Critical)

**Tasks:**
1. ✅ Add `includePaths` field to `TranspileOptions` struct (1 line)
2. ✅ Add include path to args conversion in `transpile()` (3 lines)
3. ✅ Write 5 unit tests for include path feature
4. ✅ Update API documentation (TranspilerAPI.h comments)
5. ✅ Update README with include path examples
6. ✅ Run full test suite (ensure no regression)

**Deliverables:**
- Updated `TranspilerAPI.h` with `includePaths` field
- Updated `TranspilerAPI.cpp` with args conversion
- 5 passing unit tests
- Updated documentation

**Implementation Details:**

See existing plan: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website/.planning/phases/27-wasm-vfs-integration/27-02-PLAN.md`

**Code Changes:**

```cpp
// TranspilerAPI.h
struct TranspileOptions {
    std::vector<std::string> includePaths;  // NEW
};

// TranspilerAPI.cpp (in transpile function)
for (const auto& path : options.includePaths) {
    args.push_back("-I" + path);
}
```

### 6.2 Phase 2: Documentation and Examples

**Estimated Effort:** 1 hour
**Risk:** Low
**Priority:** P1 (High)

**Tasks:**
1. Update README with `-I` flag examples
2. Add API usage examples to TranspilerAPI.h
3. Create integration test combining multi-file + include paths
4. Update CLI help text (if needed)
5. Add troubleshooting section for include path issues

**Deliverables:**
- Updated README.md
- API documentation with examples
- Integration test example
- Help text updates

### 6.3 Phase 3: Optional Enhancements (Future)

**Estimated Effort:** 3-4 hours
**Risk:** Medium
**Priority:** P2 (Medium)

**Tasks:**
1. Add include path validation (warn if directory doesn't exist)
2. Add verbose mode showing include search order
3. Create multi-file API (`transpileMultiple()`)
4. Add compilation database generation helper

**Deliverables:**
- Enhanced error reporting
- Verbose mode implementation
- Multi-file API (optional)
- Compilation database helper (optional)

---

## 7. Testing Strategy

### 7.1 Unit Tests

#### Test Suite 1: Include Path Parsing
```cpp
TEST(TranspilerAPI, SingleIncludePath) {
    TranspileOptions opts;
    opts.includePaths = {"./include"};
    // Verify -I./include in args
}

TEST(TranspilerAPI, MultipleIncludePaths) {
    TranspileOptions opts;
    opts.includePaths = {"./include", "./third_party"};
    // Verify order: -I./include -I./third_party
}

TEST(TranspilerAPI, EmptyIncludePaths) {
    TranspileOptions opts;
    // Verify no -I flags added
}

TEST(TranspilerAPI, RelativeIncludePaths) {
    TranspileOptions opts;
    opts.includePaths = {"../include", "./local"};
    // Verify relative paths work
}

TEST(TranspilerAPI, AbsoluteIncludePaths) {
    TranspileOptions opts;
    opts.includePaths = {"/usr/local/include"};
    // Verify absolute paths work
}
```

#### Test Suite 2: Include Resolution
```cpp
TEST(TranspilerAPI, StandardIncludeSyntax) {
    std::string source = R"(
        #include <myheader.h>
        int x = MACRO_FROM_HEADER;
    )";

    TranspileOptions opts;
    opts.includePaths = {"./test/fixtures/include"};
    opts.virtualFiles = {{"/test/fixtures/include/myheader.h", "#define MACRO_FROM_HEADER 42"}};

    auto result = transpile(source, "test.cpp", opts);
    EXPECT_TRUE(result.success);
    EXPECT_THAT(result.c, HasSubstr("42"));
}

TEST(TranspilerAPI, QuotedIncludeSyntax) {
    std::string source = R"(
        #include "local.h"
        int x = LOCAL_MACRO;
    )";

    // Test "local.h" vs <local.h> search behavior
}

TEST(TranspilerAPI, NestedIncludes) {
    // header1.h includes header2.h
    // Verify both resolved via include paths
}

TEST(TranspilerAPI, IncludePathSearchOrder) {
    // Same filename in multiple paths
    // Verify first path wins
}
```

### 7.2 Integration Tests

#### Test 1: Multi-File + Include Paths (CLI)
```bash
# Create test project
mkdir -p test_project/include test_project/src

# Create header
cat > test_project/include/common.h << 'EOF'
#define VERSION 100
int helper(int x);
EOF

# Create source files
cat > test_project/src/main.cpp << 'EOF'
#include <common.h>
int main() { return helper(VERSION); }
EOF

cat > test_project/src/helper.cpp << 'EOF'
#include <common.h>
int helper(int x) { return x * 2; }
EOF

# Transpile with include paths
cpptoc test_project/src/*.cpp -- -I./test_project/include

# Verify outputs
test -f main.c
test -f main.h
test -f helper.c
test -f helper.h
grep "200" main.c  # VERSION * 2
```

#### Test 2: VFS + Include Paths (API)
```cpp
TEST(Integration, VirtualFilesAndIncludePaths) {
    TranspileOptions opts;
    opts.includePaths = {"./physical/include"};
    opts.virtualFiles = {{"/virtual/extra.h", "#define EXTRA 99"}};

    std::string source = R"(
        #include <physical_header.h>
        #include "/virtual/extra.h"
        int x = PHYSICAL_MACRO + EXTRA;
    )";

    auto result = transpile(source, "test.cpp", opts);
    EXPECT_TRUE(result.success);
    // Verify both includes resolved
}
```

### 7.3 Regression Tests

**Ensure existing functionality still works:**

1. ✅ All 296 existing tests pass
2. ✅ VFS tests still pass (8 tests)
3. ✅ Header separation tests still pass (8 tests)
4. ✅ Multi-file CLI tests still pass
5. ✅ ACSL generation tests still pass
6. ✅ Exception/RTTI tests still pass

**Command:**
```bash
./scripts/run-all-tests.sh
# Expected: 296+ tests pass (existing + new)
```

---

## 8. Risk Assessment

### 8.1 Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|------------|--------|------------|
| Breaking API changes | Low | High | Use additive API changes only (new field in struct) |
| Include path search order wrong | Low | Medium | Follow clang behavior exactly, add tests |
| VFS + include path conflict | Low | Medium | Test both features together |
| Performance regression | Very Low | Low | Minimal code added, include resolution is Clang's job |
| Backward compatibility break | Very Low | High | Comprehensive regression testing |

### 8.2 Implementation Risks

| Risk | Probability | Impact | Mitigation |
|------|------------|--------|------------|
| Missing edge cases | Low | Low | Comprehensive test coverage (5+ unit tests) |
| Documentation gaps | Medium | Low | Review all docs, add examples |
| Build system issues | Very Low | Low | No build system changes required |

### 8.3 User Impact Risks

| Risk | Probability | Impact | Mitigation |
|------|------------|--------|------------|
| Confusion about `-I` syntax | Low | Low | Clear documentation, examples |
| Existing users need migration | Very Low | Low | No breaking changes, fully backward compatible |
| Platform differences (paths) | Low | Medium | Use Clang's path handling (cross-platform) |

---

## 9. Appendices

### 9.1 Current Implementation Details

#### File Handling (from investigation)
- **CLI**: Supports multiple files via `CommonOptionsParser`
- **Library**: Single file via `transpile(string)` API
- **Processing**: Each file gets independent AST
- **Output**: Separate `.c` and `.h` per file

#### Header Handling (from investigation)
- **VFS**: Fully implemented (Phase 27-01 complete)
- **Separation**: Fully implemented (Phase 28 complete)
- **Include paths**: NOT implemented (Phase 27-02 planned)

### 9.2 Clang Command-Line Patterns (from research)

**Standard Usage:**
```bash
clang file1.c file2.c -I./include -I./third_party -o program
```

**LibTooling Pattern:**
```bash
tool file.cpp -- -I./include -std=c++20
```

**Our Pattern (after implementation):**
```bash
cpptoc main.cpp -- -I./include -I./third_party -std=c++20
```

### 9.3 Related Documentation

1. **Phase 27-02 Plan**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website/.planning/phases/27-wasm-vfs-integration/27-02-PLAN.md`
2. **VFS Implementation**: Phase 27-01 (complete)
3. **Header Separation**: Phase 28 (complete)
4. **API Reference**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/TranspilerAPI.h`
5. **CLI Options**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/docs/api-reference/cli-options.md`

### 9.4 User Stories

#### Story 1: Standard Library User
> As a developer transpiling code that uses standard library headers,
> I want to specify system include directories with `-I` flags,
> So that I can use `#include <iostream>` instead of absolute paths.

#### Story 2: Multi-Module Project
> As a developer working on a multi-module C++ project,
> I want to transpile all source files with shared include directories,
> So that header resolution works consistently across all modules.

#### Story 3: WASM Developer
> As a WASM developer using the transpiler in a browser,
> I want to combine include paths with virtual files,
> So that I can mix physical headers with in-memory content seamlessly.

#### Story 4: Build System Integrator
> As a developer integrating cpptoc into CMake/Make,
> I want to use the same `-I` flags as my C++ compiler,
> So that my build scripts are consistent and maintainable.

---

## 10. Summary and Next Steps

### 10.1 Key Findings

1. **CLI Multi-File**: ✅ Already works (no changes needed)
2. **Include Paths**: ❌ Missing (critical gap, easy to implement)
3. **VFS**: ✅ Fully implemented (excellent foundation)
4. **Implementation**: Low risk, ~3 lines of code, 1-2 hours effort

### 10.2 Recommended Action

**Implement Phase 27-02 (Include Path Support) immediately:**

1. Add `includePaths` field to `TranspileOptions` (1 line)
2. Convert paths to `-I` args in `transpile()` (3 lines)
3. Write 5 unit tests
4. Update documentation
5. Run full regression tests

**Estimated Timeline:**
- Implementation: 1 hour
- Testing: 1 hour
- Documentation: 30 minutes
- **Total: 2.5 hours**

**Benefits:**
- ✅ Standard C++ include syntax
- ✅ Clang-compatible interface
- ✅ Improved WASM usability
- ✅ Better build system integration
- ✅ No breaking changes
- ✅ Minimal code complexity

### 10.3 Future Enhancements

**Not required now, but consider later:**
1. Multi-file Library API (`transpileMultiple()`)
2. Include path validation warnings
3. Verbose include search order
4. Compilation database generation

---

**Document End**

**Approval Required From:**
- [ ] Project Owner
- [ ] Technical Lead
- [ ] User Representative

**Once Approved:**
- Proceed with implementation per Phase 27-02 plan
- Track progress in GitHub Project
- Update this PRD with implementation decisions
