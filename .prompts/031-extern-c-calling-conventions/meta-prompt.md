# Meta-Prompt: Implement Full Support for extern "C" and Calling Conventions

## Overview

This meta-prompt implements a three-stage Claude-to-Claude pipeline to add comprehensive support for `extern "C"` linkage specifications and platform calling conventions (`__cdecl`, `__stdcall`, `__fastcall`, `__vectorcall`, `__pascal`, etc.) to the C++ to C transpiler.

## Context

**Project:** C++ to C Transpiler
**Feature Scope:** Language linkage and calling convention preservation
**Goal:** Correctly transpile C++ code containing `extern "C"` blocks and functions with explicit calling conventions

**Current State:**
- No explicit handling of `LinkageSpecDecl` AST nodes
- No visitor for `extern "C" { }` blocks
- No extraction of calling convention attributes
- Runtime headers use `extern "C"` guards, but transpiler doesn't process them
- Functions with C linkage may pass through or be skipped (undefined behavior)

**Research Findings Summary:**
- Clang provides `FunctionDecl::isExternC()`, `getLanguageLinkage()`, `getCallConv()` APIs
- `LinkageSpecDecl` AST node wraps `extern "C" { }` blocks
- Calling conventions stored in `FunctionProtoType::ExtInfo`
- Attributes: `StdCallAttr`, `FastCallAttr`, `RegCallAttr`, `ThisCallAttr`, `VectorCallAttr`, `PascalAttr`
- Current visitor has no `VisitLinkageSpecDecl()` method
- CNodeBuilder can create function declarations but doesn't preserve linkage/calling convention

## Stage 1: Research & Technical Investigation

### Prompt for Research Agent

```xml
<task>
<role>Clang AST Linkage and Calling Convention Researcher</role>

<objective>
Deep dive into Clang's AST representation of language linkage and calling conventions to design the transpiler implementation.

Investigate:
1. How Clang represents `extern "C"` in the AST (LinkageSpecDecl)
2. How to detect C vs C++ linkage for functions
3. How calling conventions are stored and queried
4. Platform-specific calling convention variations
5. Edge cases and special handling requirements
6. How to preserve this information in generated C code
</objective>

<background_context>
The transpiler uses RecursiveASTVisitor to walk C++ AST nodes and CNodeBuilder to create C AST nodes. Function declarations are created using FunctionDecl::Create() with storage classes but no linkage or calling convention preservation.

Existing infrastructure:
- CppToCVisitor.h: RecursiveASTVisitor-based visitor
- CNodeBuilder.h: Helper for creating C AST nodes (lines 972-1006: funcDecl())
- NameMangler.cpp: Handles function name mangling for overloads
- Runtime headers: Use conditional extern "C" guards (#ifdef __cplusplus)

Available Clang APIs (discovered):
- FunctionDecl::isExternC() - Check for C linkage
- FunctionDecl::isExternCXX() - Check for C++ linkage
- FunctionDecl::getLanguageLinkage() - Get language linkage
- FunctionDecl::getCallConv() - Get calling convention
- LinkageSpecDecl - AST node for extern "C" blocks
- DeclContext::isExternCContext() - Check if context has C linkage
</background_context>

<deliverable>
A comprehensive technical analysis document covering:

## 1. Clang AST Representation

### LinkageSpecDecl
- Structure and properties
- How to detect extern "C" vs extern "C++"
- Accessing child declarations
- Handling nested linkage specifications

### Language Linkage Detection
- FunctionDecl::getLanguageLinkage() return values
- Difference between isExternC() and C linkage
- Impact on name mangling
- Context-based linkage inheritance

### Calling Convention Representation
- CallingConv enum values (CC_C, CC_X86StdCall, CC_X86FastCall, etc.)
- FunctionType::ExtInfo structure
- Platform-specific conventions (x86, x86_64, ARM, etc.)
- Attribute classes (StdCallAttr, FastCallAttr, etc.)

## 2. Detection Strategies

### For extern "C"
- Visitor method: VisitLinkageSpecDecl()
- Query methods for functions inside blocks
- Handling forward declarations vs definitions
- Propagation to nested declarations

### For Calling Conventions
- Querying FunctionDecl::getCallConv()
- Detecting platform default vs explicit specification
- Handling function pointers with calling conventions
- Member function calling conventions (thiscall)

## 3. C Code Generation Strategy

### Options for extern "C" Functions
**Option A: Pass Through**
- Rationale: Already C-compatible
- Implementation: Skip transpilation, emit as-is
- Pros: Simple, correct
- Cons: Requires preserving original source or re-emitting

**Option B: Strip and Note**
- Rationale: extern "C" is redundant in pure C
- Implementation: Transpile function, add comment
- Pros: Clean C output
- Cons: Loses explicit C linkage marker

**Option C: Preserve with Comment**
- Rationale: Documentation value
- Implementation: Add /* extern "C" */ comment
- Pros: Maintains information
- Cons: Not semantically meaningful in C

**Recommended Approach:** [Your analysis and recommendation]

### Options for Calling Conventions
**Option A: Preserve with Attributes**
- Use GCC/Clang attribute syntax: `__attribute__((stdcall))`
- Platform-specific: `__stdcall`, `__cdecl` on Windows
- Pros: Preserves semantics
- Cons: Platform-specific output

**Option B: Document in Comments**
- Add `/* __stdcall */` before function
- Pros: Platform-independent C
- Cons: Loses functional behavior

**Option C: Runtime Mode Configuration**
- Let user choose: preserve or document
- Pros: Flexible
- Cons: More complex implementation

**Recommended Approach:** [Your analysis and recommendation]

## 4. Edge Cases and Special Handling

### extern "C" Edge Cases
- extern "C" function overloading (illegal, but compiler may accept)
- extern "C" with namespaces
- extern "C" with templates (allowed for specializations)
- extern "C" static functions
- Nested extern "C" and extern "C++" blocks

### Calling Convention Edge Cases
- Calling convention conflicts (function vs function pointer)
- Template functions with calling conventions
- Virtual functions with calling conventions
- Platform incompatibilities (stdcall on non-x86)

## 5. Testing Strategy

### Test Cases for extern "C"
1. Simple extern "C" function
2. extern "C" block with multiple functions
3. extern "C" forward declaration + C++ definition
4. Mixed C/C++ linkage in same file
5. extern "C" with function pointers
6. Static functions with extern "C"

### Test Cases for Calling Conventions
1. __cdecl (default on most platforms)
2. __stdcall (Windows API standard)
3. __fastcall (register-based)
4. __vectorcall (SIMD arguments)
5. __pascal (historical, reverse order)
6. Platform-specific behavior
7. Function pointers with calling conventions

## 6. Implementation Dependencies

### Required Changes
- [ ] Add VisitLinkageSpecDecl() to CppToCVisitor
- [ ] Extend VisitFunctionDecl() to query linkage
- [ ] Query calling convention in function processing
- [ ] Extend CNodeBuilder::funcDecl() to accept linkage/calling convention
- [ ] Add test files for linkage and calling conventions
- [ ] Update documentation (FAQ, user guide)

### Integration Points
- NameMangler: extern "C" functions should NOT be mangled
- VirtualMethodAnalyzer: Check interaction with virtual functions
- MoveSemanticTranslators: Calling conventions on move constructors
- Runtime library: Verify consistency with runtime headers

## 7. Platform Considerations

### x86 (32-bit)
- __cdecl: Caller cleans stack
- __stdcall: Callee cleans stack
- __fastcall: First 2 args in ECX/EDX
- __thiscall: Implicit for C++ member functions

### x86_64 (64-bit)
- System V ABI (Linux/macOS): RDI, RSI, RDX, RCX, R8, R9
- Microsoft x64 ABI (Windows): RCX, RDX, R8, R9
- __vectorcall: XMM registers for float/vector

### ARM
- AAPCS: R0-R3 for arguments
- Different conventions for float/SIMD

### Cross-Platform Strategy
- Detect platform-specific calling conventions
- Warn if unsupported convention used
- Provide fallback or error for incompatible conventions
</deliverable>

<constraints>
- Research official Clang documentation (clang.llvm.org/doxygen)
- Examine test files: tests/Sema/callingconv.c, tests/SemaCXX/decl-microsoft-call-conv.cpp
- Use web search for Clang AST APIs and calling convention specs
- Consider safety-critical requirements (formal verification)
- Ensure platform portability of generated C code
</constraints>

<tools_required>
- WebSearch: Clang API documentation, calling convention specs
- WebFetch: Clang doxygen pages
- Read: Existing codebase patterns
- Grep: Search for related implementations
</tools_required>

<output_file>
.prompts/031-extern-c-calling-conventions/stage1-research.md
</output_file>

<success_criteria>
- Complete understanding of Clang's linkage and calling convention APIs
- Clear recommendation for C code generation strategy
- Comprehensive edge case analysis
- Platform considerations documented
- Ready to proceed to planning stage
</success_criteria>
</task>
```

## Stage 2: Planning & Architecture Design

### Prompt for Planning Agent

```xml
<task>
<role>Feature Architect</role>

<objective>
Design the implementation architecture for adding extern "C" and calling convention support to the C++ to C transpiler.

Create:
1. Detailed implementation plan
2. API designs for new/modified components
3. Test-driven development strategy
4. Integration approach with existing code
</objective>

<input_from_stage1>
Read the research findings from:
.prompts/031-extern-c-calling-conventions/stage1-research.md
</input_from_stage1>

<deliverable>
A comprehensive implementation plan:

## 1. Architecture Overview

### High-Level Design
```
C++ AST with extern "C" and calling conventions
    ↓
VisitLinkageSpecDecl() - Detect extern "C" blocks
    ↓
VisitFunctionDecl() - Query linkage and calling convention
    ↓
CNodeBuilder::funcDeclWithLinkage() - Create C function with preserved info
    ↓
Emit C code with appropriate attributes/comments
```

### Design Decisions
Document the chosen approaches for:
- extern "C" handling (pass through / strip / preserve)
- Calling convention preservation (attributes / comments / configuration)
- Name mangling interaction (suppress for extern "C")
- Platform specificity (target-dependent output)

## 2. Component Design

### 2.1 CppToCVisitor Extensions

#### New Visitor Method
```cpp
/// Visit linkage specification (extern "C" { }) blocks
/// @param LS The linkage specification declaration
/// @return true to continue traversal
bool VisitLinkageSpecDecl(clang::LinkageSpecDecl *LS);
```

**Responsibilities:**
- Detect extern "C" vs extern "C++" blocks
- Track linkage context for nested declarations
- Handle both braced blocks and single declarations

**Implementation Strategy:**
- Check language: `LS->getLanguage() == LinkageSpecDecl::lang_c`
- Visit child declarations with linkage awareness
- Update context tracking if needed

#### Modified Visitor Method
```cpp
/// Visit function declarations (MODIFIED)
/// Now also queries language linkage and calling convention
bool VisitFunctionDecl(clang::FunctionDecl *FD);
```

**Additional Queries:**
```cpp
bool isExternC = FD->isExternC();
clang::CallingConv CC = FD->getType()->getAs<FunctionProtoType>()->getCallConv();
```

### 2.2 CNodeBuilder Extensions

#### New/Modified Function Creation
```cpp
/// Create function declaration with linkage and calling convention preservation
/// @param name Function name
/// @param retType Return type
/// @param params Parameter declarations
/// @param body Function body (optional)
/// @param isExternC Whether function has C linkage (suppresses mangling)
/// @param callConv Calling convention to preserve (optional)
/// @param body Function body (optional)
/// @return Created FunctionDecl
FunctionDecl* funcDeclWithLinkage(
    llvm::StringRef name,
    QualType retType,
    llvm::ArrayRef<ParmVarDecl*> params,
    bool isExternC = false,
    std::optional<clang::CallingConv> callConv = std::nullopt,
    Stmt* body = nullptr
);
```

**Implementation Details:**
- Use FunctionDecl::Create() as before
- Add attributes if preserving calling conventions
- Consider platform-specific attribute syntax

### 2.3 NameMangler Integration

#### Linkage-Aware Mangling
```cpp
/// Mangle function name (MODIFIED)
/// Now checks for extern "C" linkage to suppress mangling
/// @param FD Function declaration
/// @return Mangled name, or original name if extern "C"
std::string mangleFunctionName(clang::FunctionDecl *FD);
```

**Logic:**
```cpp
if (FD->isExternC()) {
    return FD->getName().str();  // No mangling for C linkage
}
// ... existing mangling logic
```

### 2.4 Configuration and Runtime Modes

#### User-Configurable Behavior
```cpp
enum class CallingConvMode {
    Preserve,   // Use __attribute__((stdcall)) etc.
    Comment,    // Add /* __stdcall */ comments
    Strip       // Omit calling convention (warn user)
};

enum class ExternCMode {
    Preserve,   // Add /* extern "C" */ comment
    Strip,      // Silently omit
    PassThrough // Don't transpile, emit original (future)
};
```

## 3. Test-Driven Development Plan

### Test Suite Organization
```
tests/
├── ExternCBasicTest.cpp          - Simple extern "C" functions
├── ExternCBlockTest.cpp          - extern "C" { } blocks
├── CallingConventionTest.cpp     - __cdecl, __stdcall, etc.
├── LinkageManglingTest.cpp       - Interaction with name mangling
└── integration/
    └── ExternCIntegrationTest.cpp - End-to-end transpilation
```

### TDD Workflow (Red-Green-Refactor)

#### Phase 1: extern "C" Detection
**RED:**
```cpp
void test_SimpleExternCFunction() {
    const char *code = R"(
        extern "C" int add(int a, int b) { return a + b; }
    )";
    // ... transpile ...
    // ASSERT: Generated C function named "add" (not mangled)
}
```

**GREEN:** Implement VisitLinkageSpecDecl() + isExternC() check

**REFACTOR:** Extract linkage detection logic

#### Phase 2: Calling Convention Detection
**RED:**
```cpp
void test_StdcallConvention() {
    const char *code = R"(
        int __stdcall WindowProc(int msg, int wparam);
    )";
    // ... transpile ...
    // ASSERT: Generated C has __attribute__((stdcall)) or /* __stdcall */
}
```

**GREEN:** Implement calling convention query and preservation

**REFACTOR:** Add configuration for preserve/comment modes

#### Phase 3: Integration Testing
**RED:**
```cpp
void test_ExternCWithOverloading() {
    const char *code = R"(
        extern "C" int process(int x);
        int process(float x);  // C++ linkage, should be mangled
    )";
    // ... transpile ...
    // ASSERT: C function "process" and "process_float"
}
```

**GREEN:** Ensure NameMangler respects extern "C"

**REFACTOR:** Handle edge cases

### Test Coverage Goals
- [ ] 100% coverage of VisitLinkageSpecDecl()
- [ ] 100% coverage of calling convention detection
- [ ] Edge cases: nested extern blocks, forward declarations
- [ ] Platform-specific tests (x86, x86_64, ARM)
- [ ] Negative tests: invalid linkage combinations

## 4. Implementation Roadmap

### Milestone 1: extern "C" Detection (Week 1)
**Tasks:**
1. Add VisitLinkageSpecDecl() to CppToCVisitor
2. Add isExternC() check in VisitFunctionDecl()
3. Write 5 basic tests (RED phase)
4. Implement detection logic (GREEN phase)
5. Verify all tests pass

**Deliverables:**
- VisitLinkageSpecDecl() implementation
- Tests: ExternCBasicTest.cpp, ExternCBlockTest.cpp
- Passing test suite (10+ tests)

### Milestone 2: Calling Convention Support (Week 2)
**Tasks:**
1. Query calling convention in VisitFunctionDecl()
2. Extend CNodeBuilder for attribute/comment generation
3. Write platform-specific tests (RED phase)
4. Implement calling convention preservation (GREEN phase)
5. Add configuration options

**Deliverables:**
- Calling convention detection and preservation
- Tests: CallingConventionTest.cpp
- Configuration: CallingConvMode enum
- Passing test suite (15+ tests)

### Milestone 3: Name Mangling Integration (Week 3)
**Tasks:**
1. Modify NameMangler to check isExternC()
2. Write integration tests (RED phase)
3. Fix mangling suppression (GREEN phase)
4. Test with overloaded functions

**Deliverables:**
- Updated NameMangler with linkage awareness
- Tests: LinkageManglingTest.cpp
- Integration tests passing

### Milestone 4: Documentation and Polish (Week 4)
**Tasks:**
1. Update FAQ.md with extern "C" / calling convention questions
2. Add user guide section
3. Document configuration options
4. Add examples to example_projects/
5. Final integration testing

**Deliverables:**
- docs/FAQ.md updated
- docs/user-guide/calling-conventions.md (new)
- examples/extern-c-example/ (new)
- All tests passing (30+ tests total)

## 5. Integration Strategy

### Existing Code Impact Analysis

#### Files to Modify
1. **include/CppToCVisitor.h** (lines 96-110)
   - Add: `bool VisitLinkageSpecDecl(clang::LinkageSpecDecl *LS);`
   - Modify: `bool VisitFunctionDecl(clang::FunctionDecl *FD);`

2. **src/CppToCVisitor.cpp** (lines 462-477)
   - Implement linkage and calling convention queries
   - Add context tracking for extern "C" blocks

3. **include/CNodeBuilder.h** (lines 972-1006)
   - Add: `funcDeclWithLinkage()` method
   - Consider: Attribute/comment helpers

4. **src/NameMangler.cpp** (lines 14-32)
   - Check `isExternC()` before mangling
   - Return original name for C linkage

5. **CMakeLists.txt**
   - Add new test files

#### Compatibility Verification
- [ ] Virtual functions: Ensure calling conventions don't break vtables
- [ ] Move semantics: Test extern "C" move constructors (should warn?)
- [ ] RAII: Calling conventions on constructors/destructors
- [ ] Exception handling: extern "C" functions and exception specs

### Regression Testing
- Run full existing test suite (71 tests)
- Verify no existing tests break
- Add CI/CD checks for new tests

## 6. Risk Assessment

### High Risk
- **Platform-specific calling conventions:** Different behavior on Windows/Linux/macOS
  - Mitigation: Extensive platform testing, clear documentation
- **Name mangling interaction:** Breaking existing overload resolution
  - Mitigation: Comprehensive integration tests

### Medium Risk
- **Virtual function interaction:** Calling conventions on virtual methods
  - Mitigation: Test virtual function calling convention preservation
- **Template instantiation:** extern "C" with templates (should fail gracefully)
  - Mitigation: Add negative tests, clear error messages

### Low Risk
- **Documentation completeness:** Users not understanding new features
  - Mitigation: FAQ updates, examples, user guide section

## 7. Acceptance Criteria

### Feature Complete When:
- [ ] All extern "C" functions detected and processed correctly
- [ ] Calling conventions queried and preserved (or documented)
- [ ] Name mangling suppressed for extern "C" functions
- [ ] 30+ tests passing (unit + integration)
- [ ] Documentation updated (FAQ, user guide)
- [ ] Example project demonstrating usage
- [ ] CI/CD pipeline includes new tests
- [ ] No regressions in existing functionality

### Definition of Done:
- Code reviewed
- Tests passing
- Documentation complete
- User-facing examples provided
- Ready for git flow release
</deliverable>

<constraints>
- Follow existing code patterns (RecursiveASTVisitor, CNodeBuilder)
- Maintain SOLID principles
- Use TDD (write tests first)
- Preserve backward compatibility
- Support safety-critical requirements (formal verification)
</constraints>

<tools_required>
- Read: Existing code patterns
- Edit: Modify visitor and builder
- Write: New test files
- Bash: Run tests
</tools_required>

<output_file>
.prompts/031-extern-c-calling-conventions/stage2-plan.md
</output_file>

<success_criteria>
- Detailed implementation plan with milestones
- API designs for all new/modified components
- Comprehensive test strategy
- Integration approach documented
- Risk assessment complete
- Ready for implementation
</success_criteria>
</task>
```

## Stage 3: Implementation Execution

### Prompt for Implementation Agent

```xml
<task>
<role>Feature Implementation Engineer</role>

<objective>
Implement full support for extern "C" and calling conventions in the C++ to C transpiler following the architecture and test plan from Stage 2.

Execute TDD workflow:
1. Write failing tests (RED)
2. Implement minimal code to pass (GREEN)
3. Refactor for quality (REFACTOR)
4. Repeat for each milestone
</objective>

<input_from_stage2>
Read the implementation plan from:
.prompts/031-extern-c-calling-conventions/stage2-plan.md

Follow the exact roadmap and API designs specified.
</input_from_stage2>

<deliverable>
Complete implementation including:

## 1. Code Changes

### Modified Files
1. **include/CppToCVisitor.h**
   - Added: `bool VisitLinkageSpecDecl(clang::LinkageSpecDecl *LS);`
   - Modified: `bool VisitFunctionDecl(clang::FunctionDecl *FD);`
   - Added: Linkage context tracking (if needed)

2. **src/CppToCVisitor.cpp**
   - Implemented: VisitLinkageSpecDecl() with language detection
   - Enhanced: VisitFunctionDecl() with isExternC() and getCallConv() queries
   - Integrated: Calling convention preservation logic

3. **include/CNodeBuilder.h**
   - Added: `funcDeclWithLinkage()` or extended `funcDecl()`
   - Added: Attribute/comment generation helpers

4. **src/NameMangler.cpp**
   - Modified: `mangleName()` to check `isExternC()`
   - Added: Linkage-aware mangling logic

### New Files
1. **tests/ExternCBasicTest.cpp** - Basic extern "C" functionality
2. **tests/ExternCBlockTest.cpp** - extern "C" { } blocks
3. **tests/CallingConventionTest.cpp** - Platform calling conventions
4. **tests/LinkageManglingTest.cpp** - Linkage + mangling interaction
5. **tests/integration/ExternCIntegrationTest.cpp** - End-to-end tests
6. **docs/user-guide/calling-conventions.md** - User documentation
7. **examples/extern-c-example/** - Example project

## 2. Test Results

### Test Execution Log
```
Running test suite...

ExternCBasicTest:
  ✓ test_SimpleExternCFunction (1/10)
  ✓ test_ExternCForwardDeclaration (2/10)
  ✓ test_ExternCWithDefinition (3/10)
  ...

ExternCBlockTest:
  ✓ test_ExternCBlock (1/8)
  ✓ test_NestedDeclarations (2/8)
  ...

CallingConventionTest:
  ✓ test_CdeclConvention (1/12)
  ✓ test_StdcallConvention (2/12)
  ✓ test_FastcallConvention (3/12)
  ...

LinkageManglingTest:
  ✓ test_ExternCNoMangling (1/6)
  ✓ test_MixedLinkageOverloading (2/6)
  ...

ExternCIntegrationTest:
  ✓ test_CompleteTranspilation (1/5)
  ...

Total: 41 tests passed, 0 failed
```

### Regression Testing
```
Running existing test suite (71 tests)...
All existing tests PASS ✓
No regressions detected.
```

## 3. Documentation

### Updated Documentation Files
- docs/FAQ.md - Added Q&A about extern "C" and calling conventions
- docs/user-guide/calling-conventions.md - New comprehensive guide
- README.md - Updated feature list
- docs/INDEX.md - Added links to new documentation

### Example Code
Provide working example in examples/extern-c-example/:
- C++ source with extern "C" functions
- Generated C code showing preservation
- Makefile demonstrating compilation
- README explaining the example

## 4. Verification

### Manual Verification
```bash
# Build transpiler
cmake --build build

# Run new tests
./build/ExternCBasicTest
./build/ExternCBlockTest
./build/CallingConventionTest

# Run full test suite
ctest --test-dir build --output-on-failure

# Verify example project
cd examples/extern-c-example
make
./test_extern_c
```

### CI/CD Integration
- Added tests to .github/workflows/ci.yml
- Verified GitHub Actions pass
- Updated test count in workflow

## 5. Implementation Notes

### Design Decisions Made
- Chose [Preserve/Comment/Strip] approach for extern "C" because...
- Chose [Preserve/Comment/Strip] approach for calling conventions because...
- Platform-specific behavior handled by...

### Edge Cases Handled
- Nested extern "C" and extern "C++" blocks
- extern "C" with function overloading (compile error)
- Calling conventions on virtual functions
- Platform incompatibilities

### Known Limitations
- [List any limitations or future work needed]

## 6. Git Commit

Created git commit with:
```
feat: add full support for extern "C" and calling conventions

- Add VisitLinkageSpecDecl() to detect extern "C" blocks
- Query language linkage and calling conventions in VisitFunctionDecl()
- Suppress name mangling for extern "C" functions
- Preserve calling conventions with attributes/comments
- Add 41 comprehensive tests (extern C + calling conventions)
- Update documentation (FAQ, user guide)
- Add examples/extern-c-example project

Tests: 112 total (71 existing + 41 new), all passing
Resolves: #[issue-number]
```

</deliverable>

<workflow>
## TDD Cycle for Each Feature

### Milestone 1: extern "C" Detection
1. **Write Test (RED)**
   ```bash
   # Create ExternCBasicTest.cpp with failing tests
   cmake --build build
   ./build/ExternCBasicTest  # Should fail
   ```

2. **Implement Feature (GREEN)**
   ```bash
   # Add VisitLinkageSpecDecl() to CppToCVisitor
   # Implement linkage detection
   cmake --build build
   ./build/ExternCBasicTest  # Should pass
   ```

3. **Refactor (REFACTOR)**
   ```bash
   # Clean up code, extract helpers
   ./build/ExternCBasicTest  # Still passes
   ```

4. **Repeat for each test case**

### Milestone 2: Calling Conventions
[Same TDD cycle]

### Milestone 3: Name Mangling Integration
[Same TDD cycle]

### Milestone 4: Documentation
[Write docs, verify examples]
</workflow>

<constraints>
- MUST follow TDD: write tests before implementation
- MUST maintain 100% backward compatibility
- MUST pass all existing tests (no regressions)
- MUST follow existing code patterns (Visitor, Builder)
- MUST use SOLID principles
- MUST update documentation
- MUST create working examples
- MUST commit code when complete
</constraints>

<tools_required>
- Read: Read existing code and plan
- Edit: Modify existing files
- Write: Create new test files and docs
- Bash: Compile, run tests, verify
- Git: Commit changes when complete
</tools_required>

<output_file>
.prompts/031-extern-c-calling-conventions/stage3-implementation.md
</output_file>

<success_criteria>
- All milestones completed
- 41+ new tests passing
- All 71 existing tests still passing
- Documentation updated
- Example project working
- Code committed to repository
- Ready for git flow release
</success_criteria>
</task>
```

## Usage Instructions

### Execute the Pipeline

#### Stage 1: Research
```bash
# In Claude Code CLI, run:
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage1-research
```

**Expected Output:** `.prompts/031-extern-c-calling-conventions/stage1-research.md` with complete technical analysis

#### Stage 2: Planning
```bash
# After reviewing Stage 1 output:
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage2-plan
```

**Expected Output:** `.prompts/031-extern-c-calling-conventions/stage2-plan.md` with detailed implementation plan

#### Stage 3: Implementation
```bash
# After reviewing and approving Stage 2 plan:
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage3-implementation
```

**Expected Output:**
- Modified code files
- New test files
- Updated documentation
- Git commit
- `.prompts/031-extern-c-calling-conventions/stage3-implementation.md` with results

### Alternative: Run All Stages Sequentially
```bash
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage1-research --sequential
# Review output, then:
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage2-plan --sequential
# Review output, then:
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage3-implementation
```

### Alternative: Run All Stages in Parallel (Advanced)
```bash
# WARNING: Stages 2 and 3 depend on previous stages, so only Stage 1 should run first
/taches-cc-resources:run-prompt 031-extern-c-calling-conventions/stage1-research
# Then run Stages 2 and 3 after reviewing Stage 1 output
```

## Key Design Principles

### Research Stage (Stage 1)
- **Objective:** Deep understanding of Clang APIs
- **Output:** Technical analysis, API documentation references, recommendations
- **Agent Type:** Research agent with web search capabilities
- **Deliverable:** Markdown document with detailed findings

### Planning Stage (Stage 2)
- **Objective:** Detailed implementation architecture
- **Output:** API designs, TDD strategy, integration plan, milestones
- **Agent Type:** Planning agent with code reading capabilities
- **Deliverable:** Implementation roadmap ready for execution

### Implementation Stage (Stage 3)
- **Objective:** Execute TDD implementation
- **Output:** Working code, passing tests, documentation, git commit
- **Agent Type:** Implementation agent with full tool access
- **Deliverable:** Complete feature ready for release

## Context Optimization

Each stage runs in a **fresh Claude context**, ensuring:
- ✅ No context bloat from previous stages
- ✅ Focused agent with clear single objective
- ✅ Optimal token usage (cheaper execution)
- ✅ Parallel execution potential (for independent tasks)
- ✅ Clear deliverable boundaries

Each agent produces a markdown report that the next agent reads, creating a **Claude-to-Claude pipeline** without human intervention.

## References

### Clang AST API Documentation
- [FunctionDecl Class Reference](https://clang.llvm.org/doxygen/classclang_1_1FunctionDecl.html)
- [LinkageSpecDecl Class Reference](https://clang.llvm.org/doxygen/classclang_1_1LinkageSpecDecl.html)
- [Introduction to Clang AST](https://clang.llvm.org/docs/IntroductionToTheClangAST.html)
- [Attributes in Clang](https://clang.llvm.org/docs/AttributeReference.html)

### Calling Conventions
- [x86 Calling Conventions - Wikipedia](https://en.wikipedia.org/wiki/X86_calling_conventions)
- [Clang Calling Convention Tests](https://github.com/llvm-mirror/clang/blob/master/test/Sema/callingconv.c)
- [Microsoft Calling Convention Tests](https://github.com/microsoft/clang/blob/master/test/SemaCXX/decl-microsoft-call-conv.cpp)

### Project Context
- Current transpiler architecture: docs/ARCHITECTURE.md
- Existing visitor patterns: include/CppToCVisitor.h
- AST node builder: include/CNodeBuilder.h
- Name mangling: src/NameMangler.cpp
- Runtime library examples: runtime/exception_runtime.h

---

**Meta-Prompt Version:** 1.0
**Created:** 2025-12-18
**Project:** C++ to C Transpiler
**Feature:** extern "C" and Calling Convention Support
