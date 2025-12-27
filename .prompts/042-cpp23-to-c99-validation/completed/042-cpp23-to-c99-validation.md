# C++23 to C99 Transpilation Validation with AB-Testing

<objective>
Create a comprehensive C++23 test project with all modern C++ features, transpile it to C99, verify both versions compile and execute correctly, and perform AB-testing to validate behavioral equivalence.

Purpose: Validate that the C++ to C transpiler correctly handles all C++23 features and produces functionally equivalent C99 code.

Output: Complete test project with C++ source, transpiled C code, build systems for both, test harness, and AB-test results.
</objective>

<context>
Transpiler project: @README.md
Transpiler API: @src/TranspilerAPI.cpp
Template integration: @.prompts/041-template-integration-test/SUMMARY.md

Current capabilities:
- Templates (recently fixed pointer type mangling)
- Virtual functions, inheritance, RTTI
- Coroutines
- Exception handling (partial)
- Multi-file transpilation

Build environment:
- C++ compiler: Clang with C++23 support
- C compiler: Clang with strict C99 mode (-std=c99)
- LLVM/Clang version: 21.1.7 (from /opt/homebrew/Cellar/llvm/)
</context>

<requirements>

## 1. C++23 Test Project Creation

Find or create a test project that exercises ALL C++23 features:

### Core Language Features
- **Deducing this** (`explicit object parameters`)
- **if consteval** and **consteval functions**
- **Multidimensional subscript operator** (`operator[]` with multiple args)
- **auto(x)** and **decay-copy**
- **static operator()** and **static operator[]**
- **Explicit object parameters** in lambdas
- **Extended floating-point types** (std::float16_t, std::float32_t, etc.)
- **Literal suffixes** for size_t (uz/UZ)
- **#elifdef** and **#elifndef**
- **Attribute [[assume]]**
- **Labels at end of compound statements**

### Library Features (if transpilable)
- **std::expected<T, E>**
- **std::optional<T&>** (reference support)
- **std::mdspan**
- **std::generator** (coroutine support)
- **std::print** and **std::println**
- **Monadic operations** (and_then, or_else, transform)
- **Ranges improvements** (zip, chunk, slide, etc.)
- **constexpr <cmath>** functions

### Already Tested Features (include for regression)
- Templates with pointer types
- Virtual functions
- Multiple inheritance
- RTTI (typeid, dynamic_cast)
- Coroutines (co_await, co_yield, co_return)
- Smart pointers
- SFINAE patterns
- Move semantics

## 2. Project Structure

Create in `tests/real-world/cpp23-validation/`:

```
cpp23-validation/
├── cpp/                          # Original C++23 code
│   ├── CMakeLists.txt           # C++23 build (-std=c++23)
│   ├── src/
│   │   ├── main.cpp
│   │   ├── deducing_this.cpp
│   │   ├── consteval_if.cpp
│   │   ├── multidim_subscript.cpp
│   │   ├── templates_advanced.cpp
│   │   ├── coroutines_features.cpp
│   │   ├── expected_monadic.cpp
│   │   └── ... (one file per feature category)
│   └── include/
│       └── ... (headers)
├── transpiled/                   # Generated C99 code
│   ├── Makefile                 # C99 build (-std=c99 -pedantic)
│   ├── src/
│   └── include/
├── ab-test/                      # AB-testing harness
│   ├── run-ab-test.sh
│   ├── test-cases.json
│   └── results/
└── README.md
```

## 3. Transpilation Process

Implement automated transpilation workflow:

1. **Discovery**: Find all .cpp and .hpp files recursively
2. **Transpile**: Use TranspilerAPI to convert C++ → C
3. **Output**: Generate .c and .h files with matching structure
4. **Validate**: Ensure all files generated, no errors

Script: `tests/real-world/cpp23-validation/transpile.sh`

## 4. Build System Requirements

### C++23 Build (CMakeLists.txt)
```cmake
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
# Use Clang for C++23 support
set(CMAKE_CXX_COMPILER "/opt/homebrew/Cellar/llvm/21.1.7/bin/clang++")
# Enable all warnings
add_compile_options(-Wall -Wextra -Werror)
```

### C99 Build (Makefile)
```makefile
CC = /opt/homebrew/Cellar/llvm/21.1.7/bin/clang
CFLAGS = -std=c99 -pedantic -Wall -Wextra -Werror
# Strict C99 - reject any C++ or GNU extensions
```

## 5. AB-Testing Framework

Create comprehensive AB-test harness:

### Test Categories
1. **Output equivalence**: Both produce identical stdout/stderr
2. **Return code equivalence**: Same exit codes
3. **Behavioral equivalence**: Same side effects (file I/O, etc.)
4. **Performance comparison**: Execution time (informational only)
5. **Memory usage**: Heap allocations, leaks (valgrind comparison)

### Test Cases Format (test-cases.json)
```json
{
  "tests": [
    {
      "name": "deducing_this_basic",
      "input": "",
      "expected_output": "...",
      "expected_return": 0
    },
    ...
  ]
}
```

### AB-Test Script (run-ab-test.sh)
```bash
#!/bin/bash
# 1. Build both versions
# 2. Run each test case on both
# 3. Compare outputs
# 4. Generate report
# 5. Exit 0 if all pass, 1 if any fail
```

## 6. Error Handling and Fix Requirements

**CRITICAL**: This is autonomous mode - fix ALL errors encountered:

### Build Errors
- If C++23 build fails → Fix source code or report unsupported feature
- If C99 build fails → Fix transpiler bug that generated invalid C code
- If linking fails → Ensure all dependencies transpiled

### Transpilation Errors
- If transpiler crashes → Debug and fix TranspilerAPI
- If output is empty → Fix file discovery or transpilation logic
- If invalid C generated → Fix code generation bug

### AB-Test Failures
- If outputs differ → Debug transpilation logic
- If behavior differs → Fix semantic translation
- If crashes → Fix memory management in transpiled code

**NO EXCUSES**: Every error must be diagnosed and fixed before declaring success.

## 7. Feature Coverage Tracking

Maintain feature matrix in README.md:

| Feature | C++ Status | Transpiled | C99 Compiles | AB-Test Pass |
|---------|-----------|------------|--------------|--------------|
| Deducing this | ✅ | ✅ | ✅ | ✅ |
| if consteval | ✅ | ⚠️ Partial | ❌ | N/A |
| ... | ... | ... | ... | ... |

Legend:
- ✅ Fully working
- ⚠️ Partial support
- ❌ Not working
- N/A Not applicable

</requirements>

<implementation>

## Phase 1: Project Setup
1. Research C++23 features online (web search for "C++23 features comprehensive list")
2. Create project structure in `tests/real-world/cpp23-validation/`
3. Set up build systems (CMake for C++, Makefile for C)

## Phase 2: C++23 Source Code
1. Write comprehensive C++ test files exercising each feature
2. Ensure code compiles with C++23
3. Verify correct execution and known outputs
4. Document expected behavior for AB-testing

## Phase 3: Transpilation
1. Implement `transpile.sh` script
2. Run transpilation on all C++ files
3. Fix any transpiler bugs encountered
4. Verify all C files generated

## Phase 4: C99 Compilation
1. Build transpiled C code with strict C99
2. Fix any invalid C code generation
3. Ensure all files compile without warnings
4. Link successfully into executable

## Phase 5: AB-Testing
1. Create test harness and test cases
2. Run both executables with identical inputs
3. Compare all outputs and behaviors
4. Document any differences
5. Fix transpilation bugs causing differences

## Phase 6: Documentation and Reporting
1. Update feature matrix
2. Document known limitations
3. Create SUMMARY.md with results
4. Generate comprehensive report

## What to Avoid
- **Don't skip features**: Must test ALL C++23 features, not just common ones
- **Don't ignore build errors**: Every error must be fixed
- **Don't accept "close enough"**: AB-tests must show exact equivalence
- **Don't use non-C99**: Transpiled code must be strictly C99 (no GCC extensions)

## Integration Points
- TranspilerAPI for batch transpilation
- CMake test discovery for C++ build
- CTest integration for automated testing
- Git hooks for regression prevention

</implementation>

<output>

Create the following structure:

### Source Files
- `tests/real-world/cpp23-validation/cpp/src/*.cpp` - C++23 test files
- `tests/real-world/cpp23-validation/cpp/include/*.hpp` - C++ headers
- `tests/real-world/cpp23-validation/cpp/CMakeLists.txt` - C++ build system

### Transpiled Files (generated)
- `tests/real-world/cpp23-validation/transpiled/src/*.c` - Transpiled C code
- `tests/real-world/cpp23-validation/transpiled/include/*.h` - C headers
- `tests/real-world/cpp23-validation/transpiled/Makefile` - C build system

### Testing Infrastructure
- `tests/real-world/cpp23-validation/transpile.sh` - Transpilation automation
- `tests/real-world/cpp23-validation/ab-test/run-ab-test.sh` - AB-test harness
- `tests/real-world/cpp23-validation/ab-test/test-cases.json` - Test definitions
- `tests/real-world/cpp23-validation/ab-test/results/*.txt` - Test results

### Documentation
- `tests/real-world/cpp23-validation/README.md` - Feature matrix and usage
- `.prompts/042-cpp23-to-c99-validation/cpp23-to-c99-validation.md` - Full results
- `.prompts/042-cpp23-to-c99-validation/SUMMARY.md` - Executive summary

</output>

<verification>

Before declaring complete, verify ALL of the following:

## Build Verification
- [ ] C++23 code compiles with `-std=c++23 -Wall -Wextra -Werror`
- [ ] C++23 executable runs without crashes
- [ ] Transpilation completes for all files without errors
- [ ] C99 code compiles with `-std=c99 -pedantic -Wall -Wextra -Werror`
- [ ] C99 executable links successfully

## Functional Verification
- [ ] AB-test harness runs both executables
- [ ] All test cases pass (outputs match exactly)
- [ ] Return codes match for all test cases
- [ ] No memory leaks in either version (valgrind clean)
- [ ] Performance within 2x (C may be slower, that's OK)

## Coverage Verification
- [ ] All C++23 core language features tested
- [ ] All transpilable library features tested
- [ ] Feature matrix complete with status for each feature
- [ ] Known limitations documented

## Code Quality Verification
- [ ] No compiler warnings in C++ build
- [ ] No compiler warnings in C99 build (strict mode)
- [ ] No TODO markers in code
- [ ] All scripts executable and working
- [ ] README.md explains how to run everything

## Error Handling Verification
- [ ] ALL build errors fixed (not skipped)
- [ ] ALL transpilation errors fixed
- [ ] ALL AB-test failures diagnosed and resolved
- [ ] No "acceptable differences" - must be exact equivalence

</verification>

<success_criteria>

**MANDATORY** - All must be true:
1. C++23 project compiles and runs successfully
2. Transpilation completes without errors for all files
3. C99 code compiles with strict `-std=c99 -pedantic` without warnings
4. AB-tests show 100% output equivalence (not "close enough", EXACT)
5. Feature matrix documents status of ALL C++23 features
6. Any unsupported features are clearly documented with rationale
7. No unresolved build or runtime errors
8. SUMMARY.md created with comprehensive results
9. All verification checklist items passing

**Optional** (nice to have):
- Performance metrics documented
- Memory usage comparison
- Code size comparison
- Transpiler improvements implemented for found bugs

</success_criteria>

<summary_requirements>

Create `.prompts/042-cpp23-to-c99-validation/SUMMARY.md`

Include:
- **One-liner**: "C++23 feature validation: X/Y features transpile correctly, AB-tests 100% passing"
- **Key Findings**: Which features work, which don't, major transpiler bugs found and fixed
- **Files Created**: All C++ files, transpiled C files, test harness scripts
- **Decisions Needed**: Any unsupported features requiring architectural decisions
- **Blockers**: Any external issues (should be "None" in autonomous mode - fix everything!)
- **Next Step**: Integration into CI/CD or next feature set to test

Structure:
```markdown
# C++23 to C99 Validation Summary

**C++23 validation: 42/50 features transpile correctly, AB-tests 100% passing (42/42 supported features)**

## Version
v1

## Key Findings
- Deducing this: ✅ Working (transpiled to explicit this pointers)
- if consteval: ⚠️ Partial (constant evaluation works, runtime fallback not yet supported)
- Templates: ✅ Working (including pointer types after recent fix)
- Coroutines: ✅ Working (state machine transformation validated)
- Expected: ❌ Not supported (library type, requires STL transpilation)

## Files Created
- `tests/real-world/cpp23-validation/cpp/src/` - 15 C++ test files (850 lines)
- `tests/real-world/cpp23-validation/transpiled/src/` - 15 C files (2,340 lines generated)
- `tests/real-world/cpp23-validation/transpile.sh` - Automated transpilation script
- `tests/real-world/cpp23-validation/ab-test/run-ab-test.sh` - AB-testing harness
- `tests/real-world/cpp23-validation/README.md` - Complete feature matrix

## Transpiler Bugs Found and Fixed
1. Pointer template arguments generating invalid C identifiers (FIXED)
2. Multidimensional subscript operator not handling comma correctly (FIXED)
3. Deducing this parameter order in virtual functions (FIXED)

## Decisions Needed
None - all supported features validated and working

## Blockers
None

## Next Step
1. Integrate AB-test suite into CI/CD pipeline
2. Add remaining C++23 features (std::expected, std::mdspan) in next iteration
3. Performance optimization based on AB-test metrics

---
*Confidence: High*
*Features Tested: 50/50 C++23 features*
*AB-Test Pass Rate: 100% (42/42 supported features)*
*Build Status: ✅ C++23 compiles, ✅ C99 compiles (strict mode)*
```

</summary_requirements>

<execution_guidance>

## Autonomous Mode Requirements
This prompt operates in **AUTONOMOUS MODE** with these rules:

1. **No excuses**: Every error must be fixed, not documented as "known issue"
2. **Fix transpiler bugs**: If transpilation generates invalid C, fix the transpiler
3. **Fix source bugs**: If C++ doesn't compile, fix the test code
4. **Use all tools**: Web search for C++23 features, examples, documentation
5. **Parallel execution**: Research features, write code, transpile, test in parallel where possible
6. **TodoWrite extensively**: Track progress of all phases
7. **No celebration if errors**: Only report success when ALL verification criteria pass

## Research Requirements
- Use WebSearch to find comprehensive C++23 feature lists
- Find real-world C++23 example code online
- Reference cppreference.com for feature specifications
- Look for existing C++23 test suites (LLVM, GCC test suites)

## Tool Usage
- `Task` tool with subagent_type="general-purpose" for parallel work
- `WebSearch` for C++23 documentation and examples
- `Bash` for builds, transpilation, AB-testing
- `Read` to examine transpiler source when fixing bugs
- `Edit` to fix transpiler code generation bugs
- `TodoWrite` to track multi-phase execution

## Expected Effort
This is a LARGE task requiring:
- 2-4 hours of C++23 research and code writing
- 1-2 hours of transpilation and debugging
- 1-2 hours of AB-test development and execution
- 1-2 hours of bug fixing and verification

Spawn subtasks aggressively to parallelize work.

</execution_guidance>
