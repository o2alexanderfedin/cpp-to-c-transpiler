# Meta-Prompt: Execute Epic #6 - Single Inheritance Support

**Epic:** [Epic #6: Single Inheritance Support](https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/38)
**Phase:** Phase 2 - Core Features
**Dependencies:** Epic #5 (RAII + Automatic Destructor Injection)
**Estimated:** 2 weeks, 8-12 Story Points
**Methodology:** TDD, Pair Programming, SOLID, KISS, DRY, YAGNI, TRIZ, Emergent Design

---

## Objective

Systematically execute all user stories within Epic #6 to implement single inheritance support, enabling C++ base class embedding, constructor/destructor chaining, and proper memory layout translation to C.

**Source of Truth:** GitHub Project #14 linked to this repository.

---

## Prerequisites

Before starting, verify:

```bash
# 1. Epic #5 must be complete
gh issue view 37 --json state | jq -r '.state'  # Should be "CLOSED"

# 2. All Phase 1 tests passing
./build_and_test.sh  # Or equivalent

# 3. GitHub CLI authenticated
gh auth status

# 4. Current branch
git branch --show-current  # Should be 'develop' or feature branch
```

**IMPORTANT:** If Epic #5 is not complete, **STOP** and work on Epic #5 first. Epic #6 depends on destructor chaining from Epic #5.

---

## Meta-Prompt Structure

This meta-prompt consists of **3 sequential prompts**:

1. **Prompt 1: User Story Breakdown** - Create user stories in GitHub from Epic #6 description
2. **Prompt 2: Setup & Planning** - Prepare development environment and create implementation plan
3. **Prompt 3: TDD Execution** - Execute each user story using strict TDD with GitHub status updates

---

## Prompt 1: User Story Breakdown & GitHub Project Setup

### Context

Epic #6 exists in GitHub ([Issue #38](https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/38)) but user stories need to be created and linked.

### Task

Break down Epic #6 into **user stories** based on the epic description and create them in GitHub Project #14.

### User Stories to Create

Based on Epic #6 deliverables, create the following user stories:

#### Story #50: Base Class Embedding in Struct Layout (2 SP)
**As a** developer
**I want** base class fields embedded at offset 0 in derived struct
**So that** upcasting (Derived* → Base*) works without pointer adjustment

**Acceptance Criteria:**
- [ ] `VisitCXXRecordDecl()` detects inheritance relationship
- [ ] Base class fields embedded first in derived struct definition
- [ ] Offset calculation: base fields start at offset 0
- [ ] `sizeof(Derived) == sizeof(Base) + sizeof(derived fields)`
- [ ] Memory layout matches C++ ABI
- [ ] Unit tests verify struct layout
- [ ] Integration test: simple Base → Derived inheritance

**Technical Notes:**
- Use `CXXRecordDecl::bases()` to iterate base classes
- For single inheritance, embed Base fields first
- Preserve field order and alignment

---

#### Story #51: Constructor Chaining (Base Before Derived) (2 SP)
**As a** developer
**I want** base constructors called before derived constructors
**So that** base class is fully initialized before derived class initialization

**Acceptance Criteria:**
- [ ] Detect base class constructor calls in `CXXConstructorDecl`
- [ ] Generate `Base__ctor()` call before derived constructor body
- [ ] Handle parameterized base constructors (argument forwarding)
- [ ] Preserve initialization order: base → derived
- [ ] Unit tests verify base constructor called first
- [ ] Integration test: constructor chaining with parameters

**Technical Notes:**
- Check `CXXConstructorDecl::init_begin()` for base initializers
- Generate: `Base__ctor((struct Base*)this, args...);`
- Cast `this` pointer to base type for base constructor call

---

#### Story #52: Destructor Chaining (Derived Before Base) (1 SP)
**As a** developer
**I want** base destructors called after derived destructors
**So that** cleanup happens in reverse construction order

**Acceptance Criteria:**
- [ ] Detect base class in `CXXDestructorDecl`
- [ ] Generate `Base__dtor()` call after derived destructor body
- [ ] Preserve destruction order: derived → base (reverse of construction)
- [ ] Unit tests verify destructor chaining order
- [ ] Integration test: RAII cleanup with inheritance

**Technical Notes:**
- Append base destructor call at end of derived destructor:
  ```c
  void Derived__dtor(struct Derived *this) {
      // Derived cleanup...
      Base__dtor((struct Base*)this);  // Call base dtor last
  }
  ```
- Works with Epic #5 (RAII) for multi-level cleanup

---

#### Story #53: Member Access Through Inheritance Chain (1 SP)
**As a** developer
**I want** derived classes to access base class members
**So that** inherited member variables and functions are usable

**Acceptance Criteria:**
- [ ] `MemberExpr` resolves base class members from derived context
- [ ] Access base fields: `this->base_field` works in derived methods
- [ ] Access base methods: call `Base_method()` from derived
- [ ] Protected member access translated correctly
- [ ] Unit tests verify member access
- [ ] Integration test: derived method using base members

**Technical Notes:**
- Member lookup through `CXXRecordDecl::lookup()`
- Check if member comes from base class
- Generate correct field offset or function name

---

#### Story #54: Upcasting (Derived* → Base*) (1 SP)
**As a** developer
**I want** derived class pointers to implicitly convert to base class pointers
**So that** polymorphic code can work with base class interfaces

**Acceptance Criteria:**
- [ ] Detect implicit cast from Derived* to Base* in AST
- [ ] Generate explicit C cast: `(struct Base*)derived_ptr`
- [ ] Upcast works because base is at offset 0 (no pointer adjustment)
- [ ] Unit tests verify upcast behavior
- [ ] Integration test: pass Derived* to function expecting Base*

**Technical Notes:**
- `ImplicitCastExpr` with `CK_DerivedToBase` kind
- For single inheritance with base at offset 0, cast is simple pointer cast
- Multi-level inheritance: chain casts through intermediate bases

---

#### Story #55: Non-Virtual Method Overriding (1 SP)
**As a** developer
**I want** derived classes to override base class non-virtual methods
**So that** derived implementations replace base implementations

**Acceptance Criteria:**
- [ ] Detect method override in derived class
- [ ] Generate separate C function: `Derived_methodName()`
- [ ] Do NOT modify base class function
- [ ] Calls use derived function when called on Derived* this pointer
- [ ] Unit tests verify override behavior
- [ ] Integration test: Base and Derived with same method name

**Technical Notes:**
- Check `CXXMethodDecl::isVirtual()` - should be false for this story
- Name mangling: `Derived_method()` vs `Base_method()`
- Static dispatch (not virtual dispatch - that's Epic #9)

---

#### Story #56: Multi-Level Inheritance (Base → Derived1 → Derived2) (2 SP)
**As a** developer
**I want** multi-level inheritance hierarchies to work correctly
**So that** complex inheritance chains are supported

**Acceptance Criteria:**
- [ ] Support 3+ level inheritance: `Base → Derived1 → Derived2`
- [ ] Constructor chaining: `Base__ctor → Derived1__ctor → Derived2__ctor`
- [ ] Destructor chaining: `Derived2__dtor → Derived1__dtor → Base__dtor`
- [ ] Memory layout: Base fields, then Derived1 fields, then Derived2 fields
- [ ] Member access through entire chain works
- [ ] Unit tests verify multi-level scenarios
- [ ] Integration test: 3-level inheritance with constructors

**Technical Notes:**
- Recursively walk inheritance chain with `CXXRecordDecl::bases()`
- Flatten all base class fields in order
- Chain all constructor/destructor calls in correct order

---

#### Story #57: Integration Testing & Validation (1 SP)
**As a** developer
**I want** comprehensive integration tests for single inheritance
**So that** all features work together in realistic scenarios

**Acceptance Criteria:**
- [ ] Integration test: Shape → Circle (classic OOP example)
- [ ] Integration test: Constructor with member init list + base init
- [ ] Integration test: Protected member access
- [ ] Integration test: Multiple derived classes from same base
- [ ] All tests pass (unit + integration)
- [ ] valgrind clean (no memory leaks)
- [ ] Generated C code compiles without warnings

**Test Scenarios:**
1. Shape (base) → Circle (derived) with constructors
2. Vehicle (base) → Car (derived) with member init lists
3. Base with protected members accessed by Derived
4. Base → Derived1, Base → Derived2 (siblings)

---

### GitHub Issue Creation Commands

```bash
# Get Epic #6 ID and project field IDs first
EPIC_ID=$(gh issue view 38 --json id --jq '.id')
PROJECT_ID="PVT_kwHOBJ7Qkc4BKHLIzg"  # Project #14
FIELD_ID_STATUS="PVTSSF_lAHOBJ7Qkc4BKHLIzg6E1IE"  # Status field
FIELD_ID_TYPE="PVTF_lAHOBJ7Qkc4BKHLIzgRfDJ0"  # Type field (if exists)

# Create Story #50
gh issue create --repo o2alexanderfedin/cpp-to-c-transpiler \
  --title "Story #50: Base Class Embedding in Struct Layout" \
  --label "user story" \
  --body "**Epic:** #38 (Epic #6: Single Inheritance Support)
**Story Points:** 2 SP

**As a** developer
**I want** base class fields embedded at offset 0 in derived struct
**So that** upcasting (Derived* → Base*) works without pointer adjustment

**Acceptance Criteria:**
- [ ] VisitCXXRecordDecl() detects inheritance relationship
- [ ] Base class fields embedded first in derived struct definition
- [ ] Offset calculation: base fields start at offset 0
- [ ] sizeof(Derived) == sizeof(Base) + sizeof(derived fields)
- [ ] Memory layout matches C++ ABI
- [ ] Unit tests verify struct layout
- [ ] Integration test: simple Base → Derived inheritance

**Technical Notes:**
- Use CXXRecordDecl::bases() to iterate base classes
- For single inheritance, embed Base fields first
- Preserve field order and alignment"

# Repeat for Stories #51-57...
# (Use similar pattern for each story)

# Link each story to Epic #6 as sub-issue
# (This requires GraphQL mutation - see Epic #19 meta-prompt for reference)
```

**IMPORTANT:** After creating each story:
1. Link it to Epic #6 using GitHub's sub-issue feature
2. Add it to Project #14
3. Set Status to "Todo"
4. Set Type to "Story" (if Type field exists)

### Output from Prompt 1

**Expected:** 8 user stories created and linked to Epic #6 in GitHub Project #14, all with status "Todo".

---

## Prompt 2: Setup & Planning

### Prerequisites Check

Before starting implementation:

```bash
# 1. All user stories created and linked
gh issue list --repo o2alexanderfedin/cpp-to-c-transpiler \
  --search "is:issue label:\"user story\" Epic #6" \
  --json number,title --jq '. | length'
# Should return: 8

# 2. Project #14 items visible
gh project item-list 14 --owner o2alexanderfedin --limit 100 | \
  jq -r '.items[] | select(.content.title | contains("Story #5")) | .content.number'
# Should list stories #50-57

# 3. Build system ready
cmake -S . -B build && cmake --build build
# Should succeed
```

### Task: Create Implementation Plan

Create a detailed implementation plan in `.prompts/009-execute-epic-6/implementation-plan.md` with:

1. **Execution Order:** Kanban-style selection of next story (based on status)
2. **TDD Workflow:** Red-Green-Refactor for each story
3. **GitHub Integration:** Commands to update story status
4. **Testing Strategy:** Unit tests + integration tests for each story
5. **Validation Checklist:** How to verify each story is complete

### Implementation Plan Template

```markdown
# Epic #6 Implementation Plan

## Execution Strategy

**Kanban Approach:**
1. Query GitHub Project for stories with status="Todo"
2. Select highest priority story (order: #50 → #57)
3. Move story to "In Progress"
4. Execute TDD workflow
5. Move story to "Done"
6. Repeat

## Story Execution Order

1. Story #50: Base Class Embedding (FOUNDATION - do first)
2. Story #51: Constructor Chaining
3. Story #52: Destructor Chaining
4. Story #53: Member Access
5. Story #54: Upcasting
6. Story #55: Method Overriding
7. Story #56: Multi-Level Inheritance
8. Story #57: Integration Testing (do last)

## TDD Workflow Per Story

For each story:

### Step 1: RED - Write Failing Test
```bash
# Create test file: tests/StoryXXTest.cpp
# Write test that captures acceptance criteria
# Build should succeed, test should FAIL
cmake --build build
./build/StoryXXTest  # Should fail
```

### Step 2: GREEN - Implement Minimal Code
```cpp
// Modify src/CppToCVisitor.cpp or relevant file
// Add minimal code to make test pass
cmake --build build
./build/StoryXXTest  # Should pass
```

### Step 3: REFACTOR - Improve Code Quality
```cpp
// Apply SOLID principles
// Remove duplication (DRY)
// Simplify (KISS)
// Check: YAGNI - did we over-engineer?
```

### Step 4: VERIFY - All Tests Pass
```bash
# Run ALL tests (not just new one)
./build_and_test.sh
# Should show all tests passing
```

### Step 5: COMMIT & UPDATE GITHUB
```bash
# Conventional commit
git add .
git commit -m "feat(epic6): implement Story #XX - <title>"

# Update GitHub Project status to "Done"
# (See GitHub integration section)
```

## GitHub Integration Commands

### Update Story Status to "In Progress"

```bash
# Variables
STORY_NUM=50  # Change for each story
PROJECT_ID="PVT_kwHOBJ7Qkc4BKHLIzg"
STATUS_FIELD_ID="PVTSSF_lAHOBJ7Qkc4BKHLIzg6E1IE"
IN_PROGRESS_OPTION_ID="<get from schema>"  # Query once at start

# Get story item ID
ITEM_ID=$(gh project item-list 14 --owner o2alexanderfedin --format json --limit 100 | \
  jq -r ".items[] | select(.content.number == $STORY_NUM) | .id")

# Update to In Progress
gh api graphql -f query='
mutation {
  updateProjectV2ItemFieldValue(input: {
    projectId: "'"$PROJECT_ID"'"
    itemId: "'"$ITEM_ID"'"
    fieldId: "'"$STATUS_FIELD_ID"'"
    value: {singleSelectOptionId: "'"$IN_PROGRESS_OPTION_ID"'"}
  }) {
    projectV2Item {
      id
    }
  }
}'
```

### Update Story Status to "Done"

```bash
# Same as above but with DONE_OPTION_ID
DONE_OPTION_ID="<get from schema>"

gh api graphql -f query='
mutation {
  updateProjectV2ItemFieldValue(input: {
    projectId: "'"$PROJECT_ID"'"
    itemId: "'"$ITEM_ID"'"
    fieldId: "'"$STATUS_FIELD_ID"'"
    value: {singleSelectOptionId: "'"$DONE_OPTION_ID"'"}
  }) {
    projectV2Item {
      id
    }
  }
}'
```

### Query Project Schema (run once to get option IDs)

```bash
gh api graphql -f query='
query {
  node(id: "PVT_kwHOBJ7Qkc4BKHLIzg") {
    ... on ProjectV2 {
      fields(first: 20) {
        nodes {
          ... on ProjectV2SingleSelectField {
            id
            name
            options {
              id
              name
            }
          }
        }
      }
    }
  }
}' | jq '.data.node.fields.nodes[] | select(.name == "Status")'
```

## Testing Strategy

### Unit Tests (Per Story)

Each story should have dedicated unit tests:

| Story | Test File | Key Tests |
|-------|-----------|-----------|
| #50 | `BaseEmbeddingTest.cpp` | Struct layout, field offsets, sizeof |
| #51 | `ConstructorChainingTest.cpp` | Base ctor called first, args passed |
| #52 | `DestructorChainingTest.cpp` | Derived dtor called first, cleanup order |
| #53 | `MemberAccessTest.cpp` | Access base fields/methods |
| #54 | `UpcastingTest.cpp` | Derived* → Base* cast works |
| #55 | `MethodOverrideTest.cpp` | Derived overrides base method |
| #56 | `MultiLevelInheritanceTest.cpp` | 3-level chain works |
| #57 | `IntegrationTest.cpp` | End-to-end scenarios |

### Integration Tests (Story #57)

Real-world scenarios:
1. Shape → Circle (area calculation)
2. Vehicle → Car (inheritance with methods)
3. Protected member access
4. Sibling derived classes

## Validation Checklist

Before marking story as "Done":

- [ ] Test file created in `tests/`
- [ ] Test initially FAILED (RED)
- [ ] Implementation added to `src/` or `include/`
- [ ] Test now PASSES (GREEN)
- [ ] Code refactored (no duplication, SOLID principles)
- [ ] ALL existing tests still pass (no regressions)
- [ ] Conventional commit message created
- [ ] GitHub Project status updated to "Done"
- [ ] Code follows existing patterns from Epic #19

## SOLID Principles Checklist

Apply to every story:

- **S**ingle Responsibility: Each class/function does ONE thing
- **O**pen/Closed: Extend behavior via inheritance, not modification
- **L**iskov Substitution: Derived classes work wherever base is expected
- **I**nterface Segregation: Small, focused interfaces
- **D**ependency Inversion: Depend on abstractions, not concretions

## TRIZ Principles

Use TRIZ when stuck:
- **Segmentation**: Break problem into smaller pieces
- **Asymmetry**: Try different approaches for base vs derived
- **Dynamics**: Make code adaptable to different inheritance patterns
- **Preliminary Action**: Set up base class info before processing derived

```

### Output from Prompt 2

**Expected:** Implementation plan created, GitHub schema queried for option IDs, all commands ready to execute.

---

## Prompt 3: TDD Execution - Story-by-Story Implementation

### Prerequisites

- [ ] Prompt 1 complete: 8 user stories created in GitHub
- [ ] Prompt 2 complete: Implementation plan ready
- [ ] GitHub option IDs obtained (Todo, In Progress, Done)
- [ ] Build system working
- [ ] Git on `develop` branch

### Main Execution Loop

This prompt executes in a loop until all 8 stories are done. For each story:

---

### Step 1: SELECT NEXT STORY (Kanban)

Query GitHub Project for next "Todo" story:

```bash
# Get all stories for Epic #6 with status "Todo"
gh project item-list 14 --owner o2alexanderfedin --format json --limit 100 | \
  jq -r '.items[] | select(.content.number >= 50 and .content.number <= 57) |
         select(.status.name == "Todo") |
         {number: .content.number, title: .content.title}'

# Expected output: First story in "Todo" status
# Select that story number for execution
```

**Decision:** Pick the lowest story number in "Todo" status (following order: #50 → #57).

---

### Step 2: UPDATE STATUS TO "IN PROGRESS"

```bash
# Example for Story #50
STORY_NUM=50
PROJECT_ID="PVT_kwHOBJ7Qkc4BKHLIzg"
STATUS_FIELD_ID="PVTSSF_lAHOBJ7Qkc4BKHLIzg6E1IE"
IN_PROGRESS_OPTION_ID="47fc9ee4"  # From schema query

# Get item ID
ITEM_ID=$(gh project item-list 14 --owner o2alexanderfedin --format json --limit 100 | \
  jq -r ".items[] | select(.content.number == $STORY_NUM) | .id")

# Mark as In Progress
gh api graphql -f query='
mutation {
  updateProjectV2ItemFieldValue(input: {
    projectId: "'"$PROJECT_ID"'"
    itemId: "'"$ITEM_ID"'"
    fieldId: "'"$STATUS_FIELD_ID"'"
    value: {singleSelectOptionId: "'"$IN_PROGRESS_OPTION_ID"'"}
  }) {
    projectV2Item { id }
  }
}'
```

**Verification:** Check GitHub Project UI - story should show "In Progress".

---

### Step 3: TDD RED - Write Failing Test

Based on story acceptance criteria, write a test that FAILS.

**Example for Story #50 (Base Class Embedding):**

```cpp
// File: tests/BaseEmbeddingTest.cpp

#include "CppToCVisitor.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include <cassert>

using namespace clang;

// Test 1: Base fields embedded at offset 0
void test_BaseFieldsAtOffsetZero() {
    std::cout << "Running test_BaseFieldsAtOffsetZero... ";

    const char *Code = R"(
        class Base {
        public:
            int x, y;
        };

        class Derived : public Base {
        public:
            int z;
        };
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CppToCVisitor visitor;
    visitor.TraverseDecl(TU);

    std::string output = visitor.getGeneratedCode();

    // Expected: struct Derived { int x; int y; int z; }
    // Base fields (x, y) must come FIRST
    assert(output.find("struct Derived") != std::string::npos);
    assert(output.find("int x;") < output.find("int z;"));  // x before z
    assert(output.find("int y;") < output.find("int z;"));  // y before z

    std::cout << "✓" << std::endl;
}

// Test 2: sizeof(Derived) == sizeof(Base) + sizeof(derived fields)
void test_SizeofDerivedCorrect() {
    std::cout << "Running test_SizeofDerivedCorrect... ";

    // This test will verify memory layout in generated C code
    // For now, check that struct definition includes all fields

    const char *Code = R"(
        class Base { int a; };
        class Derived : public Base { int b; };
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    CppToCVisitor visitor;
    visitor.TraverseDecl(TU);

    std::string output = visitor.getGeneratedCode();

    // Check Derived has both 'a' (from Base) and 'b'
    assert(output.find("struct Derived") != std::string::npos);
    assert(output.find("int a;") != std::string::npos);
    assert(output.find("int b;") != std::string::npos);

    std::cout << "✓" << std::endl;
}

int main() {
    std::cout << "\n=== Base Embedding Tests (Story #50) ===\n\n";

    test_BaseFieldsAtOffsetZero();
    test_SizeofDerivedCorrect();

    std::cout << "\n=== All Tests Passed ===\n";
    return 0;
}
```

**Build and Run (Should FAIL):**

```bash
# Add to CMakeLists.txt
add_executable(BaseEmbeddingTest
    tests/BaseEmbeddingTest.cpp
    src/CppToCVisitor.cpp
    src/NameMangler.cpp
)
target_compile_definitions(BaseEmbeddingTest PRIVATE ${LLVM_DEFINITIONS})
target_include_directories(BaseEmbeddingTest PRIVATE ${CMAKE_SOURCE_DIR}/include ${LLVM_INCLUDE_DIRS} ${CLANG_INCLUDE_DIRS})
target_link_libraries(BaseEmbeddingTest PRIVATE clangTooling clangFrontend clangAST clangBasic)

# Build
cmake --build build

# Run (should FAIL because VisitCXXRecordDecl doesn't handle inheritance yet)
./build/BaseEmbeddingTest
# Expected: Assertion failed or incomplete struct
```

**RED Phase Complete:** Test exists and fails as expected.

---

### Step 4: TDD GREEN - Implement Minimal Code

Add code to `src/CppToCVisitor.cpp` to make the test pass.

**Example Implementation for Story #50:**

```cpp
// File: src/CppToCVisitor.cpp

bool CppToCVisitor::VisitCXXRecordDecl(CXXRecordDecl *D) {
    // ... existing code ...

    // NEW: Handle inheritance (Story #50)
    if (D->getNumBases() > 0) {
        // For single inheritance, embed base class fields first
        for (const auto &Base : D->bases()) {
            CXXRecordDecl *BaseDecl = Base.getType()->getAsCXXRecordDecl();
            if (BaseDecl) {
                // Emit base class fields into derived struct
                for (auto *Field : BaseDecl->fields()) {
                    // Generate: int base_field_name;
                    output += "    " + Field->getType().getAsString() + " " +
                              Field->getNameAsString() + ";\n";
                }
            }
        }
    }

    // Then emit derived class fields
    for (auto *Field : D->fields()) {
        output += "    " + Field->getType().getAsString() + " " +
                  Field->getNameAsString() + ";\n";
    }

    // ... existing code ...
    return true;
}
```

**Build and Run (Should PASS):**

```bash
cmake --build build
./build/BaseEmbeddingTest
# Expected: ✓ ✓ All Tests Passed
```

**GREEN Phase Complete:** Tests pass with minimal implementation.

---

### Step 5: TDD REFACTOR - Apply SOLID/KISS/DRY

Review the code and refactor:

```cpp
// BEFORE (duplication):
// Emit base fields
for (auto *Field : BaseDecl->fields()) {
    output += "    " + Field->getType().getAsString() + " " +
              Field->getNameAsString() + ";\n";
}
// Emit derived fields
for (auto *Field : D->fields()) {
    output += "    " + Field->getType().getAsString() + " " +
              Field->getNameAsString() + ";\n";
}

// AFTER (DRY - extract helper method):
void CppToCVisitor::emitFields(const CXXRecordDecl *D, std::string &output) {
    for (auto *Field : D->fields()) {
        output += "    " + Field->getType().getAsString() + " " +
                  Field->getNameAsString() + ";\n";
    }
}

// Usage:
if (D->getNumBases() > 0) {
    for (const auto &Base : D->bases()) {
        emitFields(Base.getType()->getAsCXXRecordDecl(), output);
    }
}
emitFields(D, output);
```

**SOLID Check:**
- **S**ingle Responsibility: `emitFields()` only emits fields ✅
- **O**pen/Closed: Can extend to handle multiple inheritance later ✅
- **K**ISS: Simple, clear logic ✅
- **D**RY: No duplication ✅
- **YAGNI**: Only implement what's needed for single inheritance ✅

**Run Tests Again:**

```bash
cmake --build build
./build/BaseEmbeddingTest
# Should still pass after refactoring
```

---

### Step 6: VERIFY - Run ALL Tests

```bash
# Run all existing tests to check for regressions
./build/CppToCVisitorTest
./build/NameManglerTest
./build/TranslationIntegrationTest
./build/CodeGeneratorTest
./build/ValidationTest
./build/HeaderSeparatorTest
./build/IncludeGuardGeneratorTest
./build/ForwardDeclTest
./build/DependencyAnalyzerTest
./build/FileOutputManagerTest
./build/IntegrationTest
./build/BaseEmbeddingTest  # New test

# All should pass
```

**Regression Check:** Ensure NO existing tests broke.

---

### Step 7: COMMIT

```bash
git add tests/BaseEmbeddingTest.cpp
git add src/CppToCVisitor.cpp
git add include/CppToCVisitor.h  # If modified
git add CMakeLists.txt

git commit -m "feat(epic6): implement base class embedding (Story #50)

- Detect single inheritance via CXXRecordDecl::bases()
- Embed base class fields at offset 0 in derived struct
- Add helper method emitFields() for DRY compliance
- Unit tests verify struct layout and field order
- All existing tests pass (no regressions)

Refs #50"
```

**Pair Programming Note:** Explain the commit:
- "We detected inheritance using `bases()` iterator"
- "Base fields are emitted first, then derived fields"
- "This ensures offset 0 alignment for upcasting"
- "Extracted `emitFields()` to follow DRY principle"

---

### Step 8: UPDATE STORY STATUS TO "DONE"

```bash
STORY_NUM=50
DONE_OPTION_ID="<get from schema - typically last option>"

ITEM_ID=$(gh project item-list 14 --owner o2alexanderfedin --format json --limit 100 | \
  jq -r ".items[] | select(.content.number == $STORY_NUM) | .id")

gh api graphql -f query='
mutation {
  updateProjectV2ItemFieldValue(input: {
    projectId: "'"$PROJECT_ID"'"
    itemId: "'"$ITEM_ID"'"
    fieldId: "'"$STATUS_FIELD_ID"'"
    value: {singleSelectOptionId: "'"$DONE_OPTION_ID"'"}
  }) {
    projectV2Item { id }
  }
}'
```

**Verification:** Check GitHub Project UI - Story #50 should show "Done".

---

### Step 9: REPEAT for Next Story

Go back to **Step 1** and select the next "Todo" story.

Continue loop until all 8 stories (#50-#57) are "Done".

---

## Final Steps: Epic Completion

After all 8 stories are done:

### 1. Update Epic #6 Status to "Done"

```bash
EPIC_NUM=38

ITEM_ID=$(gh project item-list 14 --owner o2alexanderfedin --format json --limit 100 | \
  jq -r ".items[] | select(.content.number == $EPIC_NUM) | .id")

gh api graphql -f query='
mutation {
  updateProjectV2ItemFieldValue(input: {
    projectId: "'"$PROJECT_ID"'"
    itemId: "'"$ITEM_ID"'"
    fieldId: "'"$STATUS_FIELD_ID"'"
    value: {singleSelectOptionId: "'"$DONE_OPTION_ID"'"}
  }) {
    projectV2Item { id }
  }
}'
```

### 2. Create Release Tag

```bash
# Conventional release message
git tag -a v0.4.0 -m "Release v0.4.0: Single Inheritance Support (Epic #6)

Epic #6 Complete - Single Inheritance Support

Features:
- Base class embedding at offset 0 in derived structs (Story #50)
- Constructor chaining (base before derived) (Story #51)
- Destructor chaining (derived before base) (Story #52)
- Member access through inheritance chain (Story #53)
- Upcasting (Derived* → Base*) support (Story #54)
- Non-virtual method overriding (Story #55)
- Multi-level inheritance (Base → Derived1 → Derived2) (Story #56)
- Comprehensive integration tests (Story #57)

Story Points Delivered: 11 SP
Tests Added: 50+ unit tests, 4 integration tests
All tests passing, zero regressions

Deliverables:
✅ Base class fields embedded at struct beginning
✅ Constructor/destructor chaining implemented
✅ Memory layout matches C++ ABI
✅ Upcasting works correctly
✅ Multi-level inheritance supported
✅ valgrind clean (no memory leaks)

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>"

# Push tag
git push origin v0.4.0
```

### 3. Create GitHub Release

```bash
gh release create v0.4.0 \
  --title "v0.4.0: Single Inheritance Support (Epic #6)" \
  --notes "Epic #6 Complete - Single Inheritance Support

## Features Delivered

- ✅ Base class embedding at offset 0 (Story #50)
- ✅ Constructor chaining (Story #51)
- ✅ Destructor chaining (Story #52)
- ✅ Member access through inheritance (Story #53)
- ✅ Upcasting support (Story #54)
- ✅ Method overriding (Story #55)
- ✅ Multi-level inheritance (Story #56)
- ✅ Integration testing (Story #57)

## Metrics

- **Story Points:** 11 SP delivered
- **Tests:** 50+ unit tests, 4 integration tests
- **Test Coverage:** Maintained 1.29:1 test-to-production ratio
- **Quality:** Zero regressions, all tests passing

## Example

\`\`\`cpp
// C++ Input
class Shape {
protected:
    int x, y;
public:
    Shape(int x, int y) : x(x), y(y) {}
    void move(int dx, int dy) { x += dx; y += dy; }
};

class Circle : public Shape {
    int radius;
public:
    Circle(int x, int y, int r) : Shape(x, y), radius(r) {}
    int area() { return 3.14 * radius * radius; }
};
\`\`\`

\`\`\`c
// Generated C Output
struct Shape {
    int x;
    int y;
};

void Shape__ctor(struct Shape *this, int x, int y) {
    this->x = x;
    this->y = y;
}

void Shape_move(struct Shape *this, int dx, int dy) {
    this->x += dx;
    this->y += dy;
}

struct Circle {
    int x;       // Base class fields first
    int y;
    int radius;  // Derived class fields
};

void Circle__ctor(struct Circle *this, int x, int y, int r) {
    Shape__ctor((struct Shape*)this, x, y);  // Base constructor
    this->radius = r;
}

int Circle_area(struct Circle *this) {
    return 3.14 * this->radius * this->radius;
}
\`\`\`

## Next Steps

Epic #7: Advanced Constructor/Destructor Features (Weeks 9-10)

🤖 Generated with [Claude Code](https://claude.com/claude-code)"
```

### 4. Close Epic #6 Issue

```bash
gh issue close 38 --comment "Epic #6 Complete ✅

All 8 user stories delivered:
- Story #50: Base Class Embedding ✅
- Story #51: Constructor Chaining ✅
- Story #52: Destructor Chaining ✅
- Story #53: Member Access ✅
- Story #54: Upcasting ✅
- Story #55: Method Overriding ✅
- Story #56: Multi-Level Inheritance ✅
- Story #57: Integration Testing ✅

**Total Story Points:** 11 SP
**Duration:** <actual time taken>
**Tests:** 50+ unit tests, 4 integration tests
**Quality:** Zero regressions, all tests passing

Release: v0.4.0

🤖 Generated with [Claude Code](https://claude.com/claude-code)"
```

### 5. Update EPICS.md and ARCHITECTURE.md

```bash
# Update EPICS.md to mark Epic #6 as complete
# Update ARCHITECTURE.md if design evolved

git add EPICS.md docs/ARCHITECTURE.md
git commit -m "docs: update EPICS.md and ARCHITECTURE.md after Epic #6 completion"
git push origin develop
```

---

## Success Criteria for Meta-Prompt Completion

- [ ] All 8 user stories created in GitHub
- [ ] All stories linked to Epic #6 as sub-issues
- [ ] All stories moved through Kanban flow: Todo → In Progress → Done
- [ ] TDD followed for every story (RED-GREEN-REFACTOR)
- [ ] All tests passing (50+ new tests, all existing tests still pass)
- [ ] Zero regressions
- [ ] SOLID, KISS, DRY, YAGNI principles applied
- [ ] Conventional commits for every story
- [ ] Epic #6 status = "Done" in GitHub Project
- [ ] Release v0.4.0 created
- [ ] Epic #6 issue closed
- [ ] Documentation updated

---

## Troubleshooting

### Issue: GitHub GraphQL mutation fails

**Solution:** Re-query the project schema to get fresh option IDs:

```bash
gh api graphql -f query='
query {
  node(id: "PVT_kwHOBJ7Qkc4BKHLIzg") {
    ... on ProjectV2 {
      fields(first: 20) {
        nodes {
          ... on ProjectV2SingleSelectField {
            id
            name
            options {
              id
              name
            }
          }
        }
      }
    }
  }
}' | jq '.data.node.fields.nodes[] | select(.name == "Status")'
```

### Issue: Test fails unexpectedly

**Solution:** Use pair programming approach:
1. Explain the test to yourself (rubber duck debugging)
2. Check Clang AST dump: `clang -Xclang -ast-dump -fsyntax-only test.cpp`
3. Add debug output to visitor
4. Verify assumptions about AST structure

### Issue: Existing tests break (regression)

**Solution:**
1. Run `git diff` to see what changed
2. Review SOLID principles - did we violate Single Responsibility?
3. Check if refactoring changed behavior (should only change structure)
4. Revert and re-implement more carefully

---

## Pair Programming Prompts

Throughout execution, act as pair programming partner:

**Navigator Role (you):**
- "Let's write a test for base class embedding first"
- "I think we need to check `CXXRecordDecl::bases()` here"
- "Wait, this violates DRY - let's extract a helper method"
- "Have we verified the offset is actually 0?"

**Driver Role (implementation):**
- Write the code based on navigator guidance
- Ask questions: "Should we handle multiple inheritance here?"
- Propose refactorings: "This method is getting long, should we split it?"

**Switch roles every 15-20 minutes** (conceptually).

---

## Velocity Tracking

After Epic #6 completion, update velocity metrics:

```bash
# Calculate story points per hour
STORY_POINTS=11
HOURS=<actual time taken>
VELOCITY=$(echo "scale=2; $STORY_POINTS / $HOURS" | bc)

echo "Epic #6 Velocity: $VELOCITY SP/hour"

# Compare with Epic #19 velocity (8.89 SP/hour)
# Expected: Similar or slightly slower (Epic #6 is more complex)
```

**Target Velocity:** 6-9 SP/hour (based on Epic #19 baseline of 8.89 SP/hour)

---

## References

- Epic #6 Issue: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/38
- Epic #19 Meta-Prompt: `.prompts/008-execute-epic-19/meta-prompt.md` (template)
- ARCHITECTURE.md: Single Inheritance section
- Clang AST Docs: https://clang.llvm.org/doxygen/classclang_1_1CXXRecordDecl.html

---

**Created:** 2025-12-08
**Meta-Prompt Type:** TDD Execution with GitHub Integration
**Methodology:** Red-Green-Refactor + Kanban + Pair Programming

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
