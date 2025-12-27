# Advanced Template Integration Test

<objective>
Create a comprehensive integration test that transpiles modern C++ with advanced template features including template classes, template functions, SFINAE, auto type deduction, std::vector<T>, and multiple compilation units (2+ .cpp files, 2+ .hpp files).

**Purpose**: Validate that the C++ to C transpiler correctly handles real-world modern C++ patterns with templates, type deduction, and standard library containers across multiple files with proper header inclusion.

**Output**: A complete integration test that compiles C++ source with advanced templates, transpiles it to C, and validates the generated C code.
</objective>

<context>
**Existing template test**: @tests/TemplateIntegrationTest.cpp
- Already covers basic template instantiation
- Uses TemplateExtractor and TemplateMonomorphizer
- This new test should cover MORE ADVANCED features not in the existing test

**Project structure**:
- Integration tests live in `tests/` directory
- Use Google Test framework (gtest)
- Follow pattern from existing integration tests (CoroutineIntegrationTest.cpp, RTTIIntegrationTest.cpp)
- Tests build C++ code using `buildASTFromCodeWithArgs`

**Transpiler architecture**:
- Uses Clang frontend to parse C++ into AST
- Transforms C++ AST into C AST
- Emits C code (NOT using LLVM backend)
- Handles templates via monomorphization
</context>

<requirements>

## C++ Source Requirements

Create test C++ source code that demonstrates:

1. **Template Class with std::vector<T>**:
   - A template class that uses `std::vector<T>` as a member
   - Template parameter used in both class interface and implementation
   - At least 2 instantiations (e.g., `MyContainer<int>`, `MyContainer<std::string>`)

2. **Template Function with SFINAE**:
   - A template function using SFINAE (Substitution Failure Is Not An Error)
   - Example: `template<typename T> typename std::enable_if<std::is_integral<T>::value, T>::type foo(T x)`
   - Multiple overloads that select via SFINAE

3. **Auto Type Deduction**:
   - Use `auto` for type deduction in function returns
   - Use `auto` for variable declarations with template types
   - Example: `auto result = myTemplateFunc<int>(42);`

4. **Multiple Files**:
   - **Minimum 2 .hpp header files**:
     - One defining a template class
     - One defining template utility functions
   - **Minimum 2 .cpp implementation files**:
     - main.cpp with main() function
     - One additional .cpp that uses the templates
   - Proper `#include` directives for both system headers (`<vector>`, `<type_traits>`) and project headers

5. **System and Project Headers**:
   - System headers: `<vector>`, `<type_traits>`, `<string>` (actually used, not just included)
   - Project headers: Include between .cpp and .hpp files
   - Test that header guards work correctly

## Test Structure Requirements

1. **Google Test Integration**:
   - Use `TEST_F` or `TEST` macros
   - Clear test names describing what's being validated
   - Assertions checking correctness

2. **Multi-File Transpilation**:
   - Use transpiler API to process multiple files
   - Validate all files are transpiled correctly
   - Check that generated C code compiles

3. **Validation Checks**:
   - Template instantiations are monomorphized correctly
   - `std::vector<T>` is translated to appropriate C struct/array
   - SFINAE resolution produces correct function selections
   - `auto` types are correctly deduced and translated
   - Header includes are properly handled
   - Generated C code is syntactically valid

## Quality Requirements

1. **Follow existing patterns**:
   - Match the style of `TemplateIntegrationTest.cpp`
   - Use same helper functions (`buildAST`, `contains`) if applicable
   - Follow naming conventions

2. **Documentation**:
   - File header comment explaining what this test validates
   - Comments for each test case explaining the scenario
   - Comments explaining why specific C++ features are chosen

3. **Completeness**:
   - Test both success cases and edge cases
   - Verify generated C code structure
   - Validate that transpilation doesn't crash or error
</requirements>

<implementation>

## File Organization

Create the test in: `tests/AdvancedTemplateIntegrationTest.cpp`

## Approach

1. **Design the C++ source**:
   - Create realistic C++ code that would appear in a real project
   - Ensure it exercises all required features (templates, SFINAE, auto, std::vector, multiple files)
   - Keep it simple enough to validate but complex enough to be meaningful

2. **Multi-file handling**:
   - Use inline const char* strings for each file's content
   - Structure similar to how `MultiFileTranspilationTest.cpp` handles multiple files
   - Or use temporary files if needed

3. **Transpilation**:
   - Use the transpiler API to process the multi-file C++ project
   - Check that all files are discovered and processed
   - Validate generated C output

4. **Verification**:
   - Check generated C code contains expected monomorphized functions
   - Verify std::vector<T> is translated to C struct/array representation
   - Confirm SFINAE-selected functions are present
   - Validate header includes are handled correctly

## What to Avoid

- **Don't duplicate existing tests**: The existing `TemplateIntegrationTest.cpp` already covers basic templates
- **Don't test LLVM features**: Remember, transpiler uses Clang frontend only, NOT LLVM backend
- **Don't make it too complex**: Focus on the specific advanced features requested
- **Don't skip validation**: Must verify the generated C code is correct

## Integration with Build System

The test should:
- Compile with existing CMakeLists.txt (add to test list if needed)
- Link against necessary libraries (gtest, Clang libraries, transpiler core)
- Pass when run via `ctest` or `./scripts/run-all-tests.sh`
</implementation>

<output>
Create file:
- `tests/AdvancedTemplateIntegrationTest.cpp` - Complete integration test with:
  - File header documentation
  - Test fixture setup
  - Multiple test cases covering all requirements
  - Helper functions as needed
  - Inline C++ source code demonstrating advanced features
  - Transpilation execution
  - Validation assertions

Update if necessary:
- `CMakeLists.txt` - Add new test to build system if not auto-discovered
</output>

<verification>
Before declaring complete:

1. **Compilation**:
   - Test file compiles without errors: `cd build_working && cmake --build . --target AdvancedTemplateIntegrationTest`
   - No compiler warnings

2. **Execution**:
   - Test runs successfully: `./build_working/AdvancedTemplateIntegrationTest`
   - All test cases pass
   - No segfaults or crashes

3. **Coverage**:
   - Verify test exercises template class with std::vector<T>
   - Verify test exercises SFINAE template function
   - Verify test uses auto type deduction
   - Verify test includes 2+ .hpp and 2+ .cpp files
   - Verify test uses both system headers (<vector>, <type_traits>) and project headers
   - Verify test validates transpiled C output

4. **Integration**:
   - Test appears in `ctest -N` output
   - Test runs successfully with `./scripts/run-all-tests.sh`
   - Test count increases from 1512 to 1513+ tests

5. **Documentation**:
   - File header clearly explains purpose
   - Each test case has descriptive name and comments
   - Code is readable and maintainable
</verification>

<summary_requirements>
Create `.prompts/041-template-integration-test/SUMMARY.md`

**Required sections**:
- **One-liner**: Substantive description of what was implemented
- **Version**: v1
- **Files Created**: List test file and any other created files
- **Test Status**: Number of test cases, pass/fail status
- **Features Validated**: What C++ features are now tested
- **Decisions Needed**: Any remaining questions or choices
- **Blockers**: Any impediments encountered
- **Next Step**: What to do after this (e.g., "Run full test suite", "Add more SFINAE patterns")

**One-liner must be substantive**, not generic. Example:
- ✅ Good: "Advanced template test validates std::vector<T>, SFINAE, auto, and 4-file projects"
- ❌ Bad: "Created integration test"
</summary_requirements>

<success_criteria>
- ✅ Test file `tests/AdvancedTemplateIntegrationTest.cpp` created
- ✅ Test compiles without errors or warnings
- ✅ Test executes and all cases pass
- ✅ Test validates template class with `std::vector<T>`
- ✅ Test validates SFINAE template function
- ✅ Test validates `auto` type deduction
- ✅ Test uses minimum 2 .cpp files and 2 .hpp files
- ✅ Test uses both system headers (`<vector>`, `<type_traits>`) and project headers
- ✅ Test validates transpiled C output correctness
- ✅ Test integrated into build system (runs with `ctest`)
- ✅ Test increases total test count from 1512 to 1513+
- ✅ SUMMARY.md created with all required sections
- ✅ One-liner in SUMMARY.md is substantive and specific
</success_criteria>
