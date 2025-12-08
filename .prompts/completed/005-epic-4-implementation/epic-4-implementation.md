# Epic #4 Implementation: Clang Printer Integration & Validation

**Meta-Prompt for Systematic TDD Implementation**

## Executive Summary

Implement Epic #4 (Clang Printer Integration & Validation) following Test-Driven Development (TDD), SOLID, KISS, DRY, YAGNI, TRIZ, and Emergent Design principles. This epic integrates Clang's DeclPrinter/StmtPrinter to generate clean C code from AST #2, and validates that output compiles and behaves correctly.

**Target**: 22 story points across 6 user stories (#21-26)
**Dependencies**: Epic #1 (Infrastructure) ✅, Epic #2 (CNodeBuilder) ✅, Epic #3 (Translation) ⏸️ (50% complete)
**Architecture Reference**: [ARCHITECTURE.md - Clang Printer](docs/ARCHITECTURE.md#33-clang-printer-integration)

## Critical Success Factors

### 1. Source of Truth
**THE GITHUB PROJECT IS THE ONLY SOURCE OF TRUTH FOR EPICS AND USER STORIES.**

Before implementing ANYTHING:
```bash
# Fetch latest Epic #4 details
gh issue view 4 --json title,body,state

# Fetch all user stories for Epic #4 (stories #21-26)
gh issue view 21 --json title,body,state  # DeclPrinter/StmtPrinter integration
gh issue view 22 --json title,body,state  # PrintingPolicy C99 configuration
gh issue view 23 --json title,body,state  # #line directive injection
gh issue view 24 --json title,body,state  # Compilation validation tests
gh issue view 25 --json title,body,state  # Behavioral validation tests
gh issue view 26 --json title,body,state  # Memory safety validation
```

### 2. GitHub Issue Status Management

**CRITICAL REQUIREMENTS:**

1. **Epic Status**: Mark Epic #4 (issue #4) as in-progress when work starts:
   ```bash
   gh issue edit 4 --add-label "in-progress"
   ```

2. **Story Status**: For EACH user story (#21-26):
   - Mark as **in-progress** when work on that story starts
   - Mark as **done/closed** when work on that story completes

   ```bash
   # Starting Story #21
   gh issue edit 21 --add-label "in-progress"

   # Completing Story #21
   gh issue close 21 --comment "✅ Story completed: CodeGenerator class implemented, DeclPrinter/StmtPrinter integrated, unit tests passing, code committed to develop branch."
   ```

3. **Epic Completion**: Mark Epic #4 as done when ALL stories complete:
   ```bash
   gh issue close 4 --comment "✅ Epic #4 COMPLETE: All 6 stories (22 story points) delivered, Phase 1 POC validated successfully!"
   ```

### 3. TDD Methodology (Non-Negotiable)

**RED-GREEN-REFACTOR Cycle:**

For EVERY feature:
1. **RED**: Write a failing test that defines desired behavior
2. **GREEN**: Write minimal code to make test pass
3. **REFACTOR**: Clean up while keeping tests green

**Example for Story #21 (Printer Integration):**

```cpp
// STEP 1: RED - Write failing test
TEST(CodeGeneratorTest, PrintStructDecl) {
    // Setup
    ASTContext Context = createTestContext();
    CNodeBuilder builder(Context);

    RecordDecl *RD = builder.structDecl("Point", {
        builder.fieldDecl(Context.IntTy, "x"),
        builder.fieldDecl(Context.IntTy, "y")
    });

    // Generate code
    std::string Output;
    raw_string_ostream OS(Output);
    CodeGenerator Gen(OS, Context);
    Gen.printDecl(RD);

    // Verify
    EXPECT_THAT(Output, HasSubstr("struct Point"));
    EXPECT_THAT(Output, HasSubstr("int x"));
    EXPECT_THAT(Output, HasSubstr("int y"));
}
// Test FAILS - CodeGenerator not implemented

// STEP 2: GREEN - Minimal implementation
class CodeGenerator {
    raw_ostream &OS;
    PrintingPolicy Policy;

public:
    CodeGenerator(raw_ostream &OS, ASTContext &Ctx)
        : OS(OS), Policy(Ctx.getLangOpts()) {}

    void printDecl(Decl *D) {
        D->print(OS, Policy);
        OS << "\n";
    }
};
// Test PASSES

// STEP 3: REFACTOR - Add more features (next tests)
```

### 4. SOLID Principles Application

**Single Responsibility:**
- `CodeGenerator`: Generate C code from AST
- `ValidationTestFramework`: Compile and validate generated code
- `LineDirectiveInjector`: Add source location mapping

**Open/Closed:**
- CodeGenerator accepts any Decl/Stmt (open for extension)
- PrintingPolicy configuration separate from printing logic

**Liskov Substitution:**
- All AST nodes printable via Decl::print() / Stmt::printPretty()

**Interface Segregation:**
- Separate interfaces for printing vs validation

**Dependency Inversion:**
- CodeGenerator depends on LLVM's raw_ostream abstraction
- Tests depend on abstract validation interface

### 5. KISS/DRY/YAGNI Guidelines

**KISS (Keep It Simple):**
- Use Clang's built-in printers (don't reimplement)
- Minimal configuration for C99 output
- Straightforward validation tests

**DRY (Don't Repeat Yourself):**
- Single PrintingPolicy configuration
- Reusable test framework for validation
- Shared line directive injection logic

**YAGNI (You Aren't Gonna Need It):**
- ❌ DON'T implement custom pretty-printing (use Clang's)
- ❌ DON'T implement C code optimization (Phase 2)
- ❌ DON'T implement complex test harness (keep simple)
- ✅ DO implement only what Epic #4 acceptance criteria require

### 6. TRIZ (Ideal Final Result)

**IFR**: "Generated C code is indistinguishable from hand-written C, compiles cleanly, and behaves identically to C++."

**Contradiction Resolution:**
- *Readable vs. Correct*: Use #line directives to map to C++ source
- *Simple vs. Comprehensive*: Focus on Phase 1 scope (simple classes)
- *Fast vs. Validated*: Run validation tests after implementation, not during

**Systematic Innovation:**
- **Preliminary Action**: Configure PrintingPolicy before printing
- **Feedback**: Use compiler errors to validate output quality
- **Self-Service**: #line directives make debugging self-explanatory

## Implementation Order (Stories #21-26)

### Story #21: DeclPrinter/StmtPrinter Integration (3 points)
**Status**: OPEN
**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/21

**Objective**: Integrate Clang's DeclPrinter/StmtPrinter to output C code from AST #2.

**Acceptance Criteria**:
- [ ] Use Decl::print() to output C declarations
- [ ] Use Stmt::printPretty() to output C statements
- [ ] CodeGenerator class encapsulates printer logic
- [ ] Output to file (not stdout)
- [ ] Handle all C declaration types (struct, function, variable)
- [ ] Handle all C statement types (if, while, return, compound, etc.)

**TDD Test Cases** (implement in order):
1. `PrintStructDecl`: Print simple struct → verify output
2. `PrintFunctionDecl`: Print function → verify signature
3. `PrintTranslationUnit`: Print multiple decls → verify all present
4. `OutputToFile`: Verify file creation and contents

**Implementation Steps**:
1. Create `include/CodeGenerator.h` and `src/CodeGenerator.cpp`
2. TDD: Write PrintStructDecl test - RED
3. Implement basic CodeGenerator with printDecl() - GREEN
4. TDD: Write PrintFunctionDecl test - RED
5. Verify printDecl() works for functions - GREEN
6. TDD: Write PrintTranslationUnit test - RED
7. Implement printTranslationUnit() - GREEN
8. TDD: Write OutputToFile test - RED
9. Add file output support - GREEN

**Files to Create/Modify**:
- `include/CodeGenerator.h`: CodeGenerator class declaration
- `src/CodeGenerator.cpp`: CodeGenerator implementation
- `tests/CodeGeneratorTest.cpp`: Unit tests
- `CMakeLists.txt`: Add CodeGenerator.cpp to build

**Definition of Done**:
- [ ] CodeGenerator class implemented
- [ ] Decl::print() integrated
- [ ] Stmt::printPretty() integrated
- [ ] Output to file working
- [ ] 4 unit tests passing
- [ ] Code committed to develop branch
- [ ] Issue #21 marked as done and closed

---

### Story #22: PrintingPolicy C99 Configuration (3 points)
**Status**: OPEN
**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/22

**Objective**: Configure PrintingPolicy for valid C99 output.

**Dependencies**: Story #21 (CodeGenerator implementation)

**Acceptance Criteria**:
- [ ] Set LangOpts.C99 = true
- [ ] Disable C++ features (templates, exceptions, namespaces)
- [ ] Configure bool type (_Bool not bool)
- [ ] Configure struct/enum keywords
- [ ] Configure formatting (indentation, braces)
- [ ] Ensure output compiles with gcc -std=c99

**TDD Test Cases**:
1. `C99Enabled`: Verify LangOpts.C99 is true
2. `CppFeaturesDisabled`: Verify C++ features disabled
3. `BoolType`: Verify _Bool used instead of bool
4. `StructKeyword`: Verify 'struct' keyword present
5. `CompileWithGcc`: Generate code and compile with gcc -std=c99

**Implementation Steps**:
1. Create `createC99Policy()` helper function
2. TDD: Write C99Enabled test - RED
3. Implement LangOptions configuration - GREEN
4. TDD: Write CppFeaturesDisabled test - RED
5. Disable C++ features in LangOptions - GREEN
6. TDD: Write BoolType test - RED
7. Configure Policy.Bool = true - GREEN
8. TDD: Write StructKeyword test - RED
9. Configure Policy.SuppressTagKeyword = false - GREEN
10. TDD: Write CompileWithGcc test - RED
11. Verify generated code compiles - GREEN

**Files to Modify**:
- `include/CodeGenerator.h`: Add createC99Policy() declaration
- `src/CodeGenerator.cpp`: Implement createC99Policy()
- `tests/CodeGeneratorTest.cpp`: Add test cases

**Definition of Done**:
- [ ] PrintingPolicy configured for C99
- [ ] All C++ features disabled
- [ ] Output compiles with gcc -std=c99
- [ ] 5 unit tests passing
- [ ] Code committed to develop branch
- [ ] Issue #22 marked as done and closed

---

### Story #23: #line Directive Injection (3 points)
**Status**: OPEN
**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/23

**Objective**: Inject #line directives to map generated C back to C++ source.

**Dependencies**: Story #21 (CodeGenerator), Story #22 (PrintingPolicy)

**Acceptance Criteria**:
- [ ] Inject #line <num> "<file>" before each declaration
- [ ] Map generated C back to original C++ source locations
- [ ] Enable debugger to show C++ source when debugging C code
- [ ] Handle invalid source locations gracefully
- [ ] Preserve line numbers from original source

**TDD Test Cases**:
1. `ValidLocation`: Verify #line directive with correct line number
2. `InvalidLocation`: Verify graceful handling (no #line)
3. `MultipleDeclarations`: Verify each has correct #line
4. `FilenameEscape`: Verify filenames with spaces are quoted correctly

**Implementation Steps**:
1. Add `printWithLineDirective()` method to CodeGenerator
2. TDD: Write ValidLocation test - RED
3. Implement line directive injection for valid locations - GREEN
4. TDD: Write InvalidLocation test - RED
5. Add nullptr checks for invalid locations - GREEN
6. TDD: Write MultipleDeclarations test - RED
7. Verify each decl gets its own #line - GREEN
8. TDD: Write FilenameEscape test - RED
9. Add filename quoting logic - GREEN

**Files to Modify**:
- `include/CodeGenerator.h`: Add printWithLineDirective() declaration
- `src/CodeGenerator.cpp`: Implement printWithLineDirective()
- `tests/CodeGeneratorTest.cpp`: Add test cases

**Definition of Done**:
- [ ] #line directives injected correctly
- [ ] Source location mapping works
- [ ] Invalid locations handled gracefully
- [ ] Compiler errors map to C++ source
- [ ] 4 unit tests passing
- [ ] Code committed to develop branch
- [ ] Issue #23 marked as done and closed

---

### Story #24: Compilation Validation Tests (5 points)
**Status**: OPEN
**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/24

**Objective**: Create test framework to verify generated C code compiles.

**Dependencies**: Stories #21, #22, #23, Epic #3 (translation complete or 50% complete)

**Acceptance Criteria**:
- [ ] Test framework for compiling generated C code
- [ ] Test with gcc -std=c99
- [ ] Test with clang -std=c99
- [ ] Capture and verify compiler output
- [ ] Fail test on warnings or errors
- [ ] Test at least 5 example C++ classes

**TDD Test Cases**:
1. `EmptyClass`: Translate and compile empty class
2. `ClassWithFields`: Translate and compile class with data members
3. `ClassWithMethod`: Translate and compile class with method
4. `ClassWithConstructor`: Translate and compile class with constructor
5. `ComplexClass`: Translate and compile Rectangle with multiple methods

**Implementation Steps**:
1. Create `tests/CompilationValidationTest.cpp`
2. Implement `translateAndGenerate()` helper
3. Implement `compileC()` helper (runs gcc)
4. TDD: Write EmptyClass test - RED
5. Fix any compilation issues - GREEN
6. TDD: Write ClassWithFields test - RED
7. Fix any issues - GREEN
8. Continue for remaining tests

**Files to Create/Modify**:
- `tests/CompilationValidationTest.cpp`: End-to-end compilation tests
- `CMakeLists.txt`: Add compilation test

**Note**: Some tests may fail if Epic #3 is incomplete (Stories #17, #19, #20). That's expected - mark them as XFAIL (expected failure) and document which Epic #3 stories are needed.

**Definition of Done**:
- [ ] Compilation test framework implemented
- [ ] 5+ test cases (passing or documented as XFAIL)
- [ ] Tests run on gcc and clang
- [ ] Test failures captured with clear error messages
- [ ] Code committed to develop branch
- [ ] Issue #24 marked as done and closed

---

### Story #25: Behavioral Validation Tests (5 points)
**Status**: OPEN
**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/25

**Objective**: Verify generated C produces same output as original C++.

**Dependencies**: Story #24 (compilation tests), Epic #3 complete (or 50%)

**Acceptance Criteria**:
- [ ] Test framework for running C++ and C executables
- [ ] Compare output of C++ vs C programs
- [ ] Test at least 5 example programs
- [ ] Verify identical behavior (same output)
- [ ] Test with different input scenarios

**TDD Test Cases**:
1. `SimpleGetter`: Compare output of getter methods
2. `ConstructorInitialization`: Compare constructor initialization
3. `MultipleMethodCalls`: Compare multiple method invocations
4. `MemberModification`: Compare member variable updates
5. `OverloadedMethods`: Compare overloaded method calls

**Implementation Steps**:
1. Create `tests/BehavioralValidationTest.cpp`
2. Implement `compileAndRunCpp()` helper
3. Implement `compileAndRunC()` helper
4. Implement `compareOutputs()` helper
5. TDD: Write SimpleGetter test - RED
6. Fix any behavioral differences - GREEN
7. Continue for remaining tests

**Files to Create/Modify**:
- `tests/BehavioralValidationTest.cpp`: End-to-end behavioral tests
- `CMakeLists.txt`: Add behavioral test

**Note**: Tests may fail if Epic #3 Stories #17, #19, #20 are incomplete. Mark as XFAIL with documentation.

**Definition of Done**:
- [ ] Behavioral test framework implemented
- [ ] 5+ test cases (passing or documented as XFAIL)
- [ ] C++ and C produce identical output (where Epic #3 complete)
- [ ] Test failures show output diff
- [ ] Code committed to develop branch
- [ ] Issue #25 marked as done and closed

---

### Story #26: Memory Safety Validation (3 points)
**Status**: OPEN
**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/26

**Objective**: Verify generated C code has no memory leaks or undefined behavior.

**Dependencies**: Story #24 (compilation tests), Story #25 (behavioral tests)

**Acceptance Criteria**:
- [ ] Run generated C programs under valgrind
- [ ] Check for memory leaks
- [ ] Check for undefined behavior
- [ ] Test with at least 5 examples
- [ ] All programs must be leak-free
- [ ] Report: All heap blocks freed, no leaks possible

**TDD Test Cases**:
1. `SimpleClass`: Verify no leaks for simple class
2. `StackAllocation`: Verify stack-allocated objects don't leak
3. `NoUndefinedBehavior`: Verify valgrind reports no UB
4. `MultipleObjects`: Verify multiple objects don't leak
5. `ComplexClass`: Verify complex class with methods doesn't leak

**Implementation Steps**:
1. Create `tests/MemorySafetyTest.cpp`
2. Implement `checkMemorySafety()` helper (runs valgrind)
3. TDD: Write SimpleClass test - RED
4. Fix any memory safety issues - GREEN
5. Continue for remaining tests

**Files to Create/Modify**:
- `tests/MemorySafetyTest.cpp`: Memory safety tests
- `CMakeLists.txt`: Add memory safety test

**Note**: For Phase 1 POC with stack-allocated objects, all tests should pass (no heap allocation = no leaks).

**Definition of Done**:
- [ ] Memory safety test framework implemented
- [ ] 5+ test cases passing
- [ ] Valgrind reports no leaks
- [ ] Valgrind reports no undefined behavior
- [ ] All generated C programs are memory-safe
- [ ] Code committed to develop branch
- [ ] Issue #26 marked as done and closed

---

## Validation & Testing Strategy

### Unit Test Requirements
- **Minimum**: 3-5 test cases per story
- **Coverage**: All acceptance criteria must have corresponding tests
- **Framework**: Google Test or custom lightweight framework
- **Location**: `tests/` directory

### Integration Test Requirements
- **Scope**: Stories #24, #25, #26 (validation tests)
- **Purpose**: Validate complete pipeline (C++ → C AST → C code → compiled executable)
- **Coverage**: 5+ real-world scenarios

### Test Execution
```bash
# Build tests
cd build && cmake .. && make

# Run unit tests
./tests/CodeGeneratorTest

# Run validation tests
./tests/CompilationValidationTest
./tests/BehavioralValidationTest
./tests/MemorySafetyTest

# All tests must pass (or be marked XFAIL) before marking story as done
```

### Expected Failures Due to Epic #3 Incompleteness

If Epic #3 Stories #17, #19, #20 are incomplete:
- **Story #24 tests**: May fail for classes with constructors/methods (XFAIL acceptable)
- **Story #25 tests**: Will fail for behavioral comparison (XFAIL acceptable)
- **Story #26 tests**: Should pass for simple structs (no constructors)

Document these dependencies clearly in test comments:
```cpp
// XFAIL: Requires Epic #3 Story #17 (Constructor Translation)
TEST(CompilationValidationTest, DISABLED_ClassWithConstructor) {
    // Test will fail until Story #17 is complete
}
```

## Git Workflow & Commits

### Commit Strategy
Use **conventional commits** for all changes:

```bash
# After each story completion
git add .
git commit -m "feat(epic4): integrate DeclPrinter/StmtPrinter (Story #21)

- CodeGenerator class implemented
- Decl::print() outputs C declarations
- Stmt::printPretty() outputs C statements
- Output to file working
- 4 unit tests passing

Closes #21"

git push origin develop
```

### Commit Frequency
- Commit after EACH story completion (not after each test)
- Each commit should be a complete, working feature
- All tests must pass (or be marked XFAIL) before committing

### Branch Strategy
- Work on `develop` branch (no PRs - solo project)
- Do NOT create feature branches

## Error Handling & Edge Cases

### Common Pitfalls
1. **PrintingPolicy misconfiguration**: Verify C99 mode enabled
2. **Invalid source locations**: Check Loc.isValid() before using
3. **File I/O errors**: Check error_code when creating files
4. **Compiler not found**: Verify gcc/clang available in tests

### Edge Case Handling
```cpp
// Example: Robust line directive injection
void CodeGenerator::printWithLineDirective(Decl *D) {
    SourceLocation Loc = D->getLocation();

    // Edge case 1: Invalid source location
    if (Loc.isValid()) {
        PresumedLoc PLoc = SM.getPresumedLoc(Loc);

        // Edge case 2: PresumedLoc invalid
        if (PLoc.isValid()) {
            OS << "#line " << PLoc.getLine()
               << " \"" << PLoc.getFilename() << "\"\n";
        }
    }

    // Always print the declaration (even without #line)
    D->print(OS, Policy);
}
```

## Architecture Alignment

### Data Flow (Epic #4 Scope)
```
C++ Source File
       ↓
AST #1 (C++ AST) ← [Clang Parser]          [Epic #1]
       ↓
AST #2 (C AST)   ← [CppToCVisitor]         [Epic #3]
       ↓
C Source Code    ← [CodeGenerator]         [Epic #4] ← YOU ARE HERE
       ↓
Compiled C       ← [gcc/clang]             [Epic #4 Validation]
       ↓
Validated        ← [Behavioral/Memory]     [Epic #4 Validation]
```

### Class Structure
```
CodeGenerator
├── printDecl()                    [Story #21]
├── printStmt()                    [Story #21]
├── printTranslationUnit()         [Story #21]
├── printWithLineDirective()       [Story #23]
└── createC99Policy()              [Story #22]

ValidationTestFramework             [Stories #24, #25, #26]
├── translateAndGenerate()
├── compileC()
├── compileAndRunCpp()
├── compileAndRunC()
├── compareOutputs()
└── checkMemorySafety()
```

## Final Deliverables Checklist

### Code Deliverables
- [ ] `include/CodeGenerator.h` - Code generation class
- [ ] `src/CodeGenerator.cpp` - Code generation implementation
- [ ] `tests/CodeGeneratorTest.cpp` - Unit tests (10+ test cases)
- [ ] `tests/CompilationValidationTest.cpp` - Compilation tests (5+ test cases)
- [ ] `tests/BehavioralValidationTest.cpp` - Behavioral tests (5+ test cases)
- [ ] `tests/MemorySafetyTest.cpp` - Memory safety tests (5+ test cases)

### Documentation Deliverables
- [ ] Update `README.md` with code generation examples
- [ ] Create `EPIC-4-VERIFICATION.md` with acceptance criteria verification
- [ ] Create results summary: `.prompts/completed/005-epic-4-implementation-RESULTS.md`
- [ ] Document XFAIL tests and Epic #3 dependencies

### GitHub Deliverables
- [ ] All 6 stories (#21-26) closed with completion comments
- [ ] Epic #4 (issue #4) closed with comprehensive summary
- [ ] All code committed and pushed to develop branch
- [ ] 6+ commits (one per story)

## Success Metrics

### Quantitative Goals
- **Story Points**: 22/22 delivered
- **Acceptance Criteria**: 30+/30+ passed (6 stories × 5-6 criteria each)
- **Unit Tests**: 10+ tests passing
- **Integration Tests**: 15+ tests (passing or documented XFAIL)
- **Code Coverage**: 80%+ for CodeGenerator
- **Commits**: 6+ conventional commits

### Qualitative Goals
- Clean, readable code following SOLID principles
- Generated C code compiles without warnings
- Generated C code is indistinguishable from hand-written C
- Comprehensive validation (compilation, behavior, memory safety)
- Clear documentation of Epic #3 dependencies

### Phase 1 POC Success Criteria

**At the end of Epic #4, the tool MUST demonstrate:**
1. ✅ Parse simple C++ class
2. ✅ Generate equivalent C struct + functions
3. ✅ Generated C compiles without warnings (gcc -std=c99)
4. ✅ Generated C produces identical behavior (for completed Epic #3 features)
5. ✅ #line directives enable C++ source debugging
6. ✅ Architecture validated (Two-Phase Translation works!)

**Epic #4 Completion = Phase 1 POC Complete** 🎉

## Troubleshooting Guide

### Issue: PrintingPolicy not generating valid C99
**Solution**:
1. Verify LangOpts.C99 = 1
2. Verify LangOpts.CPlusPlus = 0
3. Check Policy.SuppressTagKeyword = false
4. Test with simple struct first, then complex cases

### Issue: #line directives incorrect
**Solution**:
1. Use SourceManager::getPresumedLoc() not getExpansionLoc()
2. Check PresumedLoc.isValid() before using
3. Verify filename escaping for paths with spaces

### Issue: Compilation tests failing
**Solution**:
1. Check if gcc/clang installed and in PATH
2. Verify generated C code syntax (print to stdout for inspection)
3. Check compiler error messages for clues
4. If Epic #3 incomplete, mark test as XFAIL

### Issue: Behavioral tests produce different output
**Solution**:
1. Check if Epic #3 Stories #17, #19 complete
2. Verify constructor translation working
3. Verify member access transformation working
4. If Epic #3 incomplete, mark test as XFAIL

### Issue: Valgrind reports leaks
**Solution**:
1. Check if heap allocation used (Phase 1 should be stack-only)
2. Verify no malloc/free in generated code
3. Check for valgrind errors vs warnings
4. For Phase 1 POC, all objects should be stack-allocated = no leaks

## Execution Instructions

**To execute this meta-prompt:**

1. **Read and understand** this entire document
2. **Verify dependencies**: Epic #1 complete ✅, Epic #2 complete ✅, Epic #3 50% complete ⏸️
3. **Mark Epic #4 as in-progress** on GitHub
4. **Implement stories IN ORDER**: #21 → #22 → #23 → #24 → #25 → #26
5. **Follow TDD religiously**: RED → GREEN → REFACTOR for every feature
6. **Mark each story as in-progress/done** on GitHub as you work
7. **Commit after each story**: One feature = one commit
8. **Run all tests** before marking story as done (XFAIL acceptable with documentation)
9. **Close all issues** with detailed comments after completion
10. **Generate results summary** documenting what was delivered
11. **Celebrate Phase 1 POC completion** 🎉

**Remember**: The GitHub Project is the ONLY source of truth. When in doubt, check the issue details on GitHub.

## Special Notes for Epic #4

### Working with Incomplete Epic #3

Epic #3 is currently 50% complete (Stories #15, #16, #18 done; Stories #17, #19, #20 pending). This means:

**What Works:**
- Class → struct conversion ✅
- Method → function conversion ✅
- Name mangling ✅

**What's Missing:**
- Constructor translation (Story #17)
- Member access transformation (Story #19)
- Integration tests (Story #20)

**Impact on Epic #4:**
- **Story #21-23**: Should work fine (printing whatever AST exists)
- **Story #24**: Some tests will fail (mark as XFAIL)
- **Story #25**: Most tests will fail (mark as XFAIL)
- **Story #26**: Should pass for simple structs

**Approach:**
1. Implement ALL 6 stories of Epic #4
2. Mark failing tests as XFAIL with clear comments
3. Document which Epic #3 stories are needed
4. Demonstrate partial POC success (simple classes work!)
5. Create "Phase 1 POC - Partial Success" report

This is acceptable! The goal is to prove the architecture works, even if some features are incomplete.

---

**Repository**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler
**Branch**: develop
**Phase**: Phase 1 POC - Week 4 (Final Week!)
**Target Date**: 2026-01-06

**Let's complete Phase 1 POC! 🚀**
