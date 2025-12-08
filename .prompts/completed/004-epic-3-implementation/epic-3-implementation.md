# Epic #3 Implementation: Simple Class Translation

**Meta-Prompt for Systematic TDD Implementation**

## Executive Summary

Implement Epic #3 (Simple Class Translation) following Test-Driven Development (TDD), SOLID, KISS, DRY, YAGNI, TRIZ, and Emergent Design principles. This epic implements core translation logic that converts simple C++ classes to C structs and member functions to C functions with `this*` parameter.

**Target**: 30 story points across 6 user stories (#15-20)
**Dependencies**: Epic #1 (Infrastructure) ✅, Epic #2 (CNodeBuilder) ✅
**Architecture Reference**: [ARCHITECTURE.md - Translation Layer](docs/ARCHITECTURE.md#32-translation-layer-recursiveastvisitor)

## Critical Success Factors

### 1. Source of Truth
**THE GITHUB PROJECT IS THE ONLY SOURCE OF TRUTH FOR EPICS AND USER STORIES.**

Before implementing ANYTHING:
```bash
# Fetch latest Epic #3 details
gh issue view 3 --json title,body,state

# Fetch all user stories for Epic #3 (stories #15-20)
gh issue view 15 --json title,body,state  # Class-to-struct conversion
gh issue view 16 --json title,body,state  # Method-to-function conversion
gh issue view 17 --json title,body,state  # Constructor translation
gh issue view 18 --json title,body,state  # Basic name mangling
gh issue view 19 --json title,body,state  # Member access transformation
gh issue view 20 --json title,body,state  # Translation integration tests
```

### 2. GitHub Issue Status Management

**CRITICAL REQUIREMENTS:**

1. **Epic Status**: Mark Epic #3 (issue #3) as in-progress when work starts:
   ```bash
   gh issue edit 3 --add-label "in-progress"
   ```

2. **Story Status**: For EACH user story (#15-20):
   - Mark as **in-progress** when work on that story starts
   - Mark as **done/closed** when work on that story completes

   ```bash
   # Starting Story #15
   gh issue edit 15 --add-label "in-progress"

   # Completing Story #15
   gh issue close 15 --comment "✅ Story completed: VisitCXXRecordDecl implemented, unit tests passing, code committed to develop branch."
   ```

3. **Epic Completion**: Mark Epic #3 as done when ALL stories complete:
   ```bash
   gh issue close 3 --comment "✅ Epic #3 COMPLETE: All 6 stories (30 story points) delivered, all acceptance criteria passed."
   ```

### 3. TDD Methodology (Non-Negotiable)

**RED-GREEN-REFACTOR Cycle:**

For EVERY feature:
1. **RED**: Write a failing test that defines desired behavior
2. **GREEN**: Write minimal code to make test pass
3. **REFACTOR**: Clean up while keeping tests green

**Example for Story #15 (Class-to-struct conversion):**

```cpp
// STEP 1: RED - Write failing test
TEST(ClassTranslationTest, EmptyClass) {
    // Setup
    const char *cpp = "class Empty {};";
    ASTContext Context = createTestContext(cpp);
    CNodeBuilder builder(Context);
    CppToCVisitor visitor(Context, builder);

    // Parse C++ and run translation
    visitor.TraverseTranslationUnit(Context.getTranslationUnitDecl());

    // Verify C struct generated
    RecordDecl *CStruct = visitor.getCStruct("Empty");
    ASSERT_TRUE(CStruct != nullptr);
    EXPECT_EQ(CStruct->getName(), "Empty");
}
// Test FAILS - CppToCVisitor::VisitCXXRecordDecl not implemented

// STEP 2: GREEN - Minimal implementation
bool CppToCVisitor::VisitCXXRecordDecl(CXXRecordDecl *D) {
    if (!D->isCompleteDefinition()) return true;

    RecordDecl *CStruct = builder.structDecl(D->getName(), {});
    cppToCMap[D] = CStruct;
    return true;
}
// Test PASSES

// STEP 3: REFACTOR - Enhance for fields (next test)
TEST(ClassTranslationTest, ClassWithFields) {
    const char *cpp = "class Point { int x, y; };";
    // ... same setup ...

    RecordDecl *CStruct = visitor.getCStruct("Point");
    ASSERT_EQ(CStruct->field_size(), 2);
}
// Test FAILS - fields not copied

// Refactor VisitCXXRecordDecl to add fields
bool CppToCVisitor::VisitCXXRecordDecl(CXXRecordDecl *D) {
    if (!D->isCompleteDefinition()) return true;

    std::vector<FieldDecl*> fields;
    for (FieldDecl *Field : D->fields()) {
        fields.push_back(builder.fieldDecl(Field->getType(), Field->getName()));
    }

    RecordDecl *CStruct = builder.structDecl(D->getName(), fields);
    cppToCMap[D] = CStruct;
    return true;
}
// Test PASSES - continue to next feature
```

### 4. SOLID Principles Application

**Single Responsibility:**
- `CppToCVisitor`: Traverse C++ AST and coordinate translation
- `NameMangler`: Generate unique C function names
- `ExprTranslator`: Transform C++ expressions to C
- `StmtTranslator`: Transform C++ statements to C

**Open/Closed:**
- New Visit methods extend functionality without modifying existing code
- New translation rules added via new methods, not by changing existing ones

**Liskov Substitution:**
- All translated C AST nodes must be valid Clang AST nodes
- Substitutable in any context expecting Clang Decl*/Stmt*/Expr*

**Interface Segregation:**
- Separate interfaces for declaration translation vs expression translation
- Don't force implementers to depend on methods they don't use

**Dependency Inversion:**
- CppToCVisitor depends on CNodeBuilder abstraction, not concrete implementations
- Makes testing easier (can mock CNodeBuilder if needed)

### 5. KISS/DRY/YAGNI Guidelines

**KISS (Keep It Simple):**
- Each Visit method does ONE thing clearly
- No premature optimization
- Readable code > clever code

**DRY (Don't Repeat Yourself):**
- Extract common patterns into helper methods
- Reuse CNodeBuilder helpers extensively
- Single source of truth for name mangling

**YAGNI (You Aren't Gonna Need It):**
- ❌ DON'T implement namespace mangling (Phase 2)
- ❌ DON'T implement virtual method translation (Phase 2)
- ❌ DON'T implement template instantiation (Phase 3)
- ✅ DO implement only what Epic #3 acceptance criteria require

### 6. TRIZ (Ideal Final Result)

**IFR**: "Translation happens with minimal code and maximum clarity."

**Contradiction Resolution:**
- *Complexity vs. Completeness*: Start simple (empty classes), evolve to complex (constructors, overloads)
- *Accuracy vs. Speed*: Use TDD to ensure accuracy, then optimize if needed
- *Flexibility vs. Simplicity*: Hard-code Phase 1 scope, design for Phase 2 extension

**Systematic Innovation:**
- **Segmentation**: Separate declaration translation from expression translation
- **Dynamics**: Build translation in stages (struct → methods → constructors → bodies)
- **Preliminary Action**: Validate C++ AST before translation (skip invalid nodes)

## Implementation Order (Stories #15-20)

### Story #15: Class-to-Struct Conversion (3 points)
**Status**: OPEN
**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/15

**Objective**: Implement `VisitCXXRecordDecl()` to convert C++ classes to C structs.

**Acceptance Criteria**:
- [ ] VisitCXXRecordDecl() handles class declarations
- [ ] Generate C struct with same member layout
- [ ] Preserve member variable names and types
- [ ] Handle access specifiers (emit all as public in C)
- [ ] Skip incomplete definitions (forward declarations)
- [ ] Store C++ class → C struct mapping

**TDD Test Cases** (implement in order):
1. `EmptyClass`: `class Empty {};` → `struct Empty {};`
2. `ClassWithFields`: `class Point { int x, y; };` → `struct Point { int x; int y; };`
3. `MixedAccessSpecifiers`: All members public/private/protected → all public in C
4. `ForwardDeclaration`: `class Forward;` → skip (no struct generated)

**Implementation Steps**:
1. Write first test (EmptyClass) - RED
2. Implement minimal VisitCXXRecordDecl (check isCompleteDefinition, create empty struct) - GREEN
3. Refactor if needed
4. Write second test (ClassWithFields) - RED
5. Enhance VisitCXXRecordDecl (add field copying) - GREEN
6. Continue for remaining tests

**Files to Modify**:
- `include/CppToCVisitor.h`: Add `VisitCXXRecordDecl()` declaration, add `cppToCMap` member
- `src/CppToCVisitor.cpp`: Implement `VisitCXXRecordDecl()`
- `tests/CppToCVisitorTest.cpp`: Add test cases

**Definition of Done**:
- [ ] VisitCXXRecordDecl implemented
- [ ] C struct preserves field order and types
- [ ] C++ to C mapping stored in `cppToCMap`
- [ ] 4 unit tests passing
- [ ] Code committed to develop branch
- [ ] Issue #15 marked as done and closed

---

### Story #18: Basic Name Mangling (3 points)
**Status**: OPEN
**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/18

**Objective**: Implement NameMangler class for generating unique C function names.

**Rationale**: Implement name mangling BEFORE method translation so Story #16 can use it immediately.

**Acceptance Criteria**:
- [ ] Simple mangling: ClassName_methodName
- [ ] Handle overloads: append parameter types (e.g., _int_float)
- [ ] Handle constructors: ClassName__ctor
- [ ] Handle destructors: ClassName__dtor (future)
- [ ] No namespace mangling yet (Phase 1 scope)
- [ ] Unique names for all methods in a class

**TDD Test Cases**:
1. `SimpleMethod`: `Point::getX()` → `Point_getX`
2. `OverloadedMethods`: `Math::add(int,int)` and `Math::add(float,float)` → unique names
3. `Constructor`: `Point::Point(int,int)` → `Point__ctor`
4. `UniquenessCheck`: Multiple calls generate unique names

**Implementation Steps**:
1. Create `include/NameMangler.h` and `src/NameMangler.cpp`
2. TDD: Write SimpleMethod test - RED
3. Implement basic mangleName() - GREEN
4. TDD: Write OverloadedMethods test - RED
5. Enhance mangleName() to append types - GREEN
6. TDD: Write Constructor test - RED
7. Implement mangleConstructor() - GREEN
8. TDD: Write UniquenessCheck test - RED
9. Add collision detection - GREEN

**Files to Create/Modify**:
- `include/NameMangler.h`: NameMangler class declaration
- `src/NameMangler.cpp`: NameMangler implementation
- `tests/NameManglerTest.cpp`: Unit tests
- `CMakeLists.txt`: Add NameMangler.cpp to build

**Definition of Done**:
- [ ] NameMangler class implemented
- [ ] Handles simple methods, overloads, constructors
- [ ] All generated names are unique
- [ ] 4 unit tests passing
- [ ] Code committed to develop branch
- [ ] Issue #18 marked as done and closed

---

### Story #16: Method-to-Function Conversion (5 points)
**Status**: OPEN
**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/16

**Objective**: Implement `VisitCXXMethodDecl()` to convert C++ methods to C functions.

**Dependencies**: Story #15 (class mapping), Story #18 (name mangling)

**Acceptance Criteria**:
- [ ] VisitCXXMethodDecl() handles member functions
- [ ] Add `struct ClassName *this` as first parameter
- [ ] Preserve original parameters after this
- [ ] Generate function name using name mangling
- [ ] Skip virtual methods (Phase 1 POC scope)
- [ ] Translate method body (expression translation in Story #19)

**TDD Test Cases**:
1. `SimpleMethod`: `int getX()` → `int Point_getX(struct Point *this)`
2. `MethodWithParams`: `void setX(int x)` → `void Point_setX(struct Point *this, int x)`
3. `ConstMethod`: `int getX() const` → `int Point_getX(const struct Point *this)`
4. `SkipVirtual`: `virtual void foo()` → skip (no function generated)

**Implementation Steps**:
1. Write first test (SimpleMethod) - RED
2. Implement minimal VisitCXXMethodDecl (check virtual, create function with this param) - GREEN
3. Write second test (MethodWithParams) - RED
4. Enhance to add original parameters - GREEN
5. Continue for remaining tests

**Files to Modify**:
- `include/CppToCVisitor.h`: Add `VisitCXXMethodDecl()`, add `NameMangler` member
- `src/CppToCVisitor.cpp`: Implement `VisitCXXMethodDecl()`
- `tests/CppToCVisitorTest.cpp`: Add test cases

**Definition of Done**:
- [ ] VisitCXXMethodDecl implemented
- [ ] C function has correct signature (this + params)
- [ ] Name mangling applied
- [ ] Virtual methods skipped
- [ ] 4 unit tests passing
- [ ] Code committed to develop branch
- [ ] Issue #16 marked as done and closed

---

### Story #17: Constructor Translation (5 points)
**Status**: OPEN
**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/17

**Objective**: Implement `VisitCXXConstructorDecl()` to convert C++ constructors to C init functions.

**Dependencies**: Story #15, #16, #18

**Acceptance Criteria**:
- [ ] VisitCXXConstructorDecl() handles constructors
- [ ] Generate `ClassName__ctor(struct ClassName *this, ...params)`
- [ ] Translate member initializers to assignments
- [ ] Translate constructor body
- [ ] Handle default constructor (no params)
- [ ] Handle parameterized constructors

**TDD Test Cases**:
1. `DefaultConstructor`: `Point() {}` → `void Point__ctor(struct Point *this) {}`
2. `MemberInitializers`: `Point(int x, int y) : x(x), y(y) {}` → assignments in body
3. `ConstructorWithBody`: Constructor with statements → statements translated

**Implementation Steps**:
1. Write first test (DefaultConstructor) - RED
2. Implement minimal VisitCXXConstructorDecl - GREEN
3. Write second test (MemberInitializers) - RED
4. Enhance to translate member initializers to assignments - GREEN
5. Write third test (ConstructorWithBody) - RED
6. Enhance to translate body statements - GREEN

**Files to Modify**:
- `include/CppToCVisitor.h`: Add `VisitCXXConstructorDecl()`
- `src/CppToCVisitor.cpp`: Implement `VisitCXXConstructorDecl()`
- `tests/CppToCVisitorTest.cpp`: Add test cases

**Definition of Done**:
- [ ] VisitCXXConstructorDecl implemented
- [ ] Member initializers translated to assignments
- [ ] Constructor body translated
- [ ] 3 unit tests passing
- [ ] Code committed to develop branch
- [ ] Issue #17 marked as done and closed

---

### Story #19: Member Access Transformation (5 points)
**Status**: OPEN
**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/19

**Objective**: Implement expression translation to transform C++ member access to C `this->member`.

**Dependencies**: Story #15, #16, #17

**Acceptance Criteria**:
- [ ] Translate MemberExpr (obj.member) to this->member
- [ ] Handle implicit this in method bodies
- [ ] Transform member variable references
- [ ] Transform member function calls
- [ ] Preserve expression types and value categories

**TDD Test Cases**:
1. `ImplicitThisRead`: `return x;` → `return this->x;`
2. `ImplicitThisWrite`: `x = val;` → `this->x = val;`
3. `ExplicitMemberAccess`: `obj.x` → `obj.x` (if obj is struct)
4. `MemberFunctionCall`: `obj.method()` → `ClassName_method(&obj)`

**Implementation Steps**:
1. Create `translateExpr()` helper method
2. TDD: Write ImplicitThisRead test - RED
3. Implement translateDeclRefExpr() to handle implicit this - GREEN
4. TDD: Write ImplicitThisWrite test - RED
5. Enhance for assignment expressions - GREEN
6. Continue for remaining tests

**Files to Modify**:
- `include/CppToCVisitor.h`: Add `translateExpr()`, `translateMemberExpr()`, `translateDeclRefExpr()`
- `src/CppToCVisitor.cpp`: Implement translation methods
- `tests/CppToCVisitorTest.cpp`: Add test cases

**Definition of Done**:
- [ ] MemberExpr translated to this->member
- [ ] Implicit this made explicit
- [ ] Expression types preserved
- [ ] 4 unit tests passing
- [ ] Code committed to develop branch
- [ ] Issue #19 marked as done and closed

---

### Story #20: Translation Integration Tests (5 points)
**Status**: OPEN
**GitHub Issue**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/20

**Objective**: Create end-to-end integration tests for complete C++ → C translation.

**Dependencies**: Stories #15-19 complete

**Acceptance Criteria**:
- [ ] Integration test framework setup
- [ ] Test complete C++ class → C struct + functions transformation
- [ ] Validate generated C AST structure
- [ ] Test C++ to C mapping correctness
- [ ] End-to-end test cases (5+ scenarios)
- [ ] AST validation (no null nodes, correct types)

**TDD Test Cases**:
1. `EmptyClass`: Full translation of empty class
2. `SimpleClassWithMethod`: Class with one getter method
3. `ConstructorTranslation`: Class with constructor and member initializers
4. `OverloadedMethods`: Class with overloaded methods → unique C names
5. `ComplexClass`: Rectangle with constructor + 3 methods

**Implementation Steps**:
1. Create integration test framework (parse real C++, run visitor, validate C AST)
2. TDD: Write EmptyClass test - RED (if not already passing)
3. Fix any issues - GREEN
4. Write SimpleClassWithMethod test - RED (should pass if Stories #15-19 done correctly)
5. Continue for remaining tests
6. Add AST validation (check no nullptr nodes, correct types)

**Files to Create/Modify**:
- `tests/TranslationIntegrationTest.cpp`: End-to-end tests
- `CMakeLists.txt`: Add integration test

**Definition of Done**:
- [ ] Integration test framework setup
- [ ] 5 end-to-end test cases passing
- [ ] AST validation implemented
- [ ] Test coverage for all translation scenarios
- [ ] Code committed to develop branch
- [ ] Issue #20 marked as done and closed

---

## Validation & Testing Strategy

### Unit Test Requirements
- **Minimum**: 3 test cases per story
- **Coverage**: All acceptance criteria must have corresponding tests
- **Framework**: Google Test (already configured from Epic #1)
- **Location**: `tests/` directory

### Integration Test Requirements
- **Scope**: Story #20 only (after all stories complete)
- **Purpose**: Validate complete translation pipeline
- **Coverage**: 5+ real-world C++ → C scenarios

### Test Execution
```bash
# Build tests
cd build && cmake .. && make

# Run unit tests
./tests/CppToCVisitorTest
./tests/NameManglerTest

# Run integration tests
./tests/TranslationIntegrationTest

# All tests must pass before marking story as done
```

### AST Validation Checklist
For every generated C AST node:
- [ ] Node is not nullptr
- [ ] Type is valid and matches expected C type
- [ ] References to other nodes are valid (no dangling pointers)
- [ ] Node can be printed without crashing (via Decl::print())

## Git Workflow & Commits

### Commit Strategy
Use **conventional commits** for all changes:

```bash
# After each story completion
git add .
git commit -m "feat(epic3): implement class-to-struct conversion (Story #15)

- VisitCXXRecordDecl handles class declarations
- Generate C struct with same member layout
- Preserve field names and types
- Store C++ to C mapping
- 4 unit tests passing

Closes #15"

git push origin develop
```

### Commit Frequency
- Commit after EACH story completion (not after each test)
- Each commit should be a complete, working feature
- All tests must pass before committing

### Branch Strategy
- Work on `develop` branch (no PRs - solo project)
- Do NOT create feature branches

## Error Handling & Edge Cases

### Common Pitfalls
1. **Nullptr checks**: Always verify AST nodes before dereferencing
2. **Incomplete definitions**: Check `isCompleteDefinition()` for classes
3. **Virtual methods**: Skip in Phase 1 (check `isVirtual()`)
4. **Implicit nodes**: Check `isImplicit()` to avoid translating compiler-generated code

### Edge Case Handling
```cpp
// Example: Robust VisitCXXRecordDecl
bool CppToCVisitor::VisitCXXRecordDecl(CXXRecordDecl *D) {
    // Edge case 1: Forward declarations
    if (!D->isCompleteDefinition()) return true;

    // Edge case 2: Compiler-generated classes
    if (D->isImplicit()) return true;

    // Edge case 3: Already translated (avoid duplicates)
    if (cppToCMap.find(D) != cppToCMap.end()) return true;

    // Normal translation logic
    // ...

    return true;
}
```

## Architecture Alignment

### Data Flow (Epic #3 Scope)
```
C++ Source File
       ↓
AST #1 (C++ AST) ← [Clang Parser]
       ↓
AST #2 (C AST)   ← [CppToCVisitor] ← You are implementing THIS
       ↓
C Source Code    ← [Clang Printer] (Epic #4)
```

### Class Structure
```
CppToCVisitor (RecursiveASTVisitor)
├── VisitCXXRecordDecl()      [Story #15]
├── VisitCXXMethodDecl()       [Story #16]
├── VisitCXXConstructorDecl()  [Story #17]
├── translateExpr()            [Story #19]
│   ├── translateMemberExpr()
│   └── translateDeclRefExpr()
└── translateStmt()            [Story #19]

NameMangler                     [Story #18]
├── mangleName()
└── mangleConstructor()

CNodeBuilder                    [Epic #2 - Already Implemented ✅]
├── structDecl()
├── funcDecl()
├── arrowMember()
└── ... 33 more helpers
```

### Mapping Storage
```cpp
class CppToCVisitor {
    // Store mappings for method translation
    std::map<CXXRecordDecl*, RecordDecl*> cppToCMap;      // C++ class → C struct
    std::map<CXXMethodDecl*, FunctionDecl*> methodMap;    // C++ method → C function
    std::map<CXXConstructorDecl*, FunctionDecl*> ctorMap; // C++ ctor → C init func
};
```

## Final Deliverables Checklist

### Code Deliverables
- [ ] `include/CppToCVisitor.h` - Updated with Visit methods
- [ ] `src/CppToCVisitor.cpp` - Implementation of Visit methods
- [ ] `include/NameMangler.h` - Name mangling class
- [ ] `src/NameMangler.cpp` - Name mangling implementation
- [ ] `tests/CppToCVisitorTest.cpp` - Unit tests (15+ test cases)
- [ ] `tests/NameManglerTest.cpp` - Name mangling tests (4+ test cases)
- [ ] `tests/TranslationIntegrationTest.cpp` - Integration tests (5+ test cases)

### Documentation Deliverables
- [ ] Update `README.md` with translation examples
- [ ] Create `EPIC-3-VERIFICATION.md` with acceptance criteria verification
- [ ] Create results summary: `.prompts/completed/004-epic-3-implementation-RESULTS.md`

### GitHub Deliverables
- [ ] All 6 stories (#15-20) closed with completion comments
- [ ] Epic #3 (issue #3) closed with comprehensive summary
- [ ] All code committed and pushed to develop branch
- [ ] 6+ commits (one per story)

## Success Metrics

### Quantitative Goals
- **Story Points**: 30/30 delivered
- **Acceptance Criteria**: 30/30 passed (6 stories × 5-6 criteria each)
- **Unit Tests**: 20+ tests passing
- **Integration Tests**: 5+ tests passing
- **Code Coverage**: 80%+ for translation logic
- **Commits**: 6+ conventional commits

### Qualitative Goals
- Clean, readable code following SOLID principles
- Zero compiler warnings
- Zero memory leaks (valgrind clean)
- Comprehensive test coverage
- Clear separation of concerns

## Troubleshooting Guide

### Issue: Tests failing after implementation
**Solution**:
1. Check if CNodeBuilder helpers are used correctly
2. Verify AST node types match expected types
3. Add debug prints to see what's being generated
4. Run tests individually to isolate failures

### Issue: Name collisions in mangling
**Solution**:
1. Check NameMangler's usedNames tracking
2. Verify parameter type encoding is unique
3. Add counter suffix for duplicates

### Issue: Nullptr crashes in translation
**Solution**:
1. Add nullptr checks before dereferencing
2. Validate isCompleteDefinition() for classes
3. Check isImplicit() to skip compiler-generated code

### Issue: Generated C AST is invalid
**Solution**:
1. Use Decl::dump() to inspect generated nodes
2. Verify all CNodeBuilder calls use valid parameters
3. Check SourceLocation is valid (can use SourceLocation() for synthetic nodes)

## Execution Instructions

**To execute this meta-prompt:**

1. **Read and understand** this entire document
2. **Verify dependencies**: Epic #1 and Epic #2 are complete
3. **Mark Epic #3 as in-progress** on GitHub
4. **Implement stories IN ORDER**: #15 → #18 → #16 → #17 → #19 → #20
5. **Follow TDD religiously**: RED → GREEN → REFACTOR for every feature
6. **Mark each story as in-progress/done** on GitHub as you work
7. **Commit after each story**: One feature = one commit
8. **Run all tests** before marking story as done
9. **Close all issues** with detailed comments after completion
10. **Generate results summary** documenting what was delivered

**Remember**: The GitHub Project is the ONLY source of truth. When in doubt, check the issue details on GitHub.

---

**Repository**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler
**Branch**: develop
**Phase**: Phase 1 POC - Week 3
**Target Date**: 2025-12-30

**Let's build Epic #3! 🚀**
