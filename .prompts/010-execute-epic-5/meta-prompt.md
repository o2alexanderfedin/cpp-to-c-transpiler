# Meta-Prompt: Execute Epic #5 - RAII + Automatic Destructor Injection

**Epic:** [Epic #5: RAII + Automatic Destructor Injection](https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/37)
**Phase:** Phase 2 - Core Features
**Dependencies:** Phase 1 POC Complete (Epics #1-4)
**Estimated:** 2 weeks, 10-13 Story Points
**Methodology:** TDD, Pair Programming, SOLID, KISS, DRY, YAGNI, TRIZ, Emergent Design

---

## Objective

Systematically execute all user stories within Epic #5 to implement RAII (Resource Acquisition Is Initialization) support by analyzing control flow and automatically injecting destructor calls at all scope exit points.

**Source of Truth:** GitHub Project #14 linked to this repository.

---

## Prerequisites

Before starting, verify:

```bash
# 1. Phase 1 POC must be complete (Epics #1-4)
gh issue view 4 --json state | jq -r '.state'  # Should be "CLOSED"

# 2. All Phase 1 tests passing
./build_and_test.sh  # Or equivalent

# 3. GitHub CLI authenticated
gh auth status

# 4. Current branch
git branch --show-current  # Should be 'develop' or feature branch
```

**IMPORTANT:** If Epic #4 is not complete, **STOP** and complete Phase 1 POC first. Epic #5 builds on the foundation established in Epics #1-4.

---

## Meta-Prompt Structure

This meta-prompt consists of **3 sequential prompts**:

1. **Prompt 1: User Story Breakdown** - Create user stories in GitHub from Epic #5 description
2. **Prompt 2: Setup & Planning** - Prepare development environment and create implementation plan
3. **Prompt 3: TDD Execution** - Execute each user story using strict TDD with GitHub status updates

---

## Prompt 1: User Story Breakdown & GitHub Project Setup

### Context

Epic #5 exists in GitHub ([Issue #37](https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/37)) but user stories need to be created and linked.

### Task

Break down Epic #5 into **user stories** based on the epic description and create them in GitHub Project #14.

### User Stories to Create

Based on Epic #5 deliverables, create the following user stories:

#### Story #43: CFG (Control Flow Graph) Analysis Infrastructure (3 SP)
**As a** developer
**I want** to analyze control flow graphs to identify all scope exit points
**So that** destructor injection points can be determined accurately

**Acceptance Criteria:**
- [ ] CFG analysis detects all function exit points (return, end of scope)
- [ ] CFG analysis detects control flow statements (goto, break, continue)
- [ ] CFG tracks all local object declarations in scope
- [ ] CFG identifies nested scopes correctly
- [ ] CFG handles multiple return paths
- [ ] Unit tests verify CFG construction for complex functions
- [ ] Integration test: analyze function with early returns

**Technical Notes:**
- Use Clang's CFG API: `clang::CFG::buildCFG()`
- Iterate CFG blocks to find terminator statements
- Track variable declarations per scope
- Consider using `CFGBlock::getTerminator()` for exit detection

---

#### Story #44: Destructor Injection at Function Exit (2 SP)
**As a** developer
**I want** destructors automatically injected at normal function exit
**So that** objects are properly cleaned up when function returns normally

**Acceptance Criteria:**
- [ ] Detect all local objects with destructors in function
- [ ] Inject destructor calls at end of function (before final return)
- [ ] Destruction order is reverse of construction order
- [ ] No duplicate destructor calls
- [ ] Unit tests verify single object destruction
- [ ] Integration test: function with multiple objects

**Technical Notes:**
- Track construction order in stack/vector
- Generate destructor calls in reverse order
- Example:
  ```c
  void func() {
      struct A a; A__ctor(&a);
      struct B b; B__ctor(&b);
      // ... function body ...
      B__dtor(&b);  // Injected: destroy b first
      A__dtor(&a);  // Injected: destroy a second
  }
  ```

---

#### Story #45: Destructor Injection at Early Returns (2 SP)
**As a** developer
**I want** destructors automatically injected before early return statements
**So that** objects are properly cleaned up when function exits early

**Acceptance Criteria:**
- [ ] Detect all return statements in function
- [ ] Inject destructor calls before each return
- [ ] Only destroy objects constructed before the return point
- [ ] Destruction order is reverse of construction
- [ ] Unit tests verify early return scenarios
- [ ] Integration test: multiple return paths with different object lifetimes

**Technical Notes:**
- For each return statement, analyze which objects are in scope
- Generate destructor sequence for objects constructed up to that point
- Example:
  ```c
  void func(int flag) {
      struct A a; A__ctor(&a);
      if (flag) {
          struct B b; B__ctor(&b);
          B__dtor(&b);  // Injected: destroy b
          A__dtor(&a);  // Injected: destroy a
          return;
      }
      A__dtor(&a);  // Injected at normal exit
  }
  ```

---

#### Story #46: Nested Scope Destruction (2 SP)
**As a** developer
**I want** objects destroyed when leaving nested scopes
**So that** inner scope objects are cleaned up before outer scope objects

**Acceptance Criteria:**
- [ ] Detect nested compound statements (scopes)
- [ ] Inject destructor calls at end of each scope
- [ ] Destruction happens before exiting scope
- [ ] Nested destruction order: innermost to outermost
- [ ] Unit tests verify nested scope scenarios
- [ ] Integration test: deeply nested scopes with objects

**Technical Notes:**
- Track scope depth and object lifetimes
- Generate destructor calls at closing brace of each scope
- Example:
  ```c
  void func() {
      struct A a; A__ctor(&a);
      {
          struct B b; B__ctor(&b);
          B__dtor(&b);  // Injected: destroy b at end of inner scope
      }
      A__dtor(&a);  // Injected: destroy a at end of function
  }
  ```

---

#### Story #47: Goto Statement Handling (1 SP)
**As a** developer
**I want** destructors injected when goto jumps out of scope
**So that** objects are cleaned up when control flow transfers via goto

**Acceptance Criteria:**
- [ ] Detect goto statements and their target labels
- [ ] Inject destructors for all objects between goto and label
- [ ] Handle forward jumps (skip object construction)
- [ ] Handle backward jumps (already constructed)
- [ ] Unit tests verify goto with object cleanup
- [ ] Integration test: complex goto patterns

**Technical Notes:**
- Analyze label position relative to goto
- Determine which objects are in scope at both points
- For jump out of scope: destroy objects before goto
- For jump into scope: error or skip (C++ forbids)
- Example:
  ```c
  void func(int flag) {
      struct A a; A__ctor(&a);
      if (flag) {
          A__dtor(&a);  // Injected: destroy a before goto
          goto cleanup;
      }
      // ... more code ...
  cleanup:
      return;
  }
  ```

---

#### Story #48: Loop Break/Continue Handling (1 SP)
**As a** developer
**I want** destructors injected before break/continue in loops
**So that** loop-local objects are cleaned up when exiting loop early

**Acceptance Criteria:**
- [ ] Detect break statements in loops
- [ ] Detect continue statements in loops
- [ ] Inject destructors for loop iteration objects before break
- [ ] Inject destructors for loop iteration objects before continue
- [ ] Unit tests verify break/continue with objects
- [ ] Integration test: loops with early exits and objects

**Technical Notes:**
- Break: destroy all loop-iteration objects
- Continue: destroy iteration objects, preserve loop-scope objects
- Example:
  ```c
  while (condition) {
      struct A a; A__ctor(&a);
      if (flag) {
          A__dtor(&a);  // Injected: destroy a before break
          break;
      }
      A__dtor(&a);  // Injected: normal iteration end
  }
  ```

---

#### Story #49: Integration Testing & Validation (2 SP)
**As a** developer
**I want** comprehensive integration tests for RAII scenarios
**So that** all destructor injection features work together in realistic code

**Acceptance Criteria:**
- [ ] Integration test: RAII file handle (open/close)
- [ ] Integration test: RAII buffer (allocate/free)
- [ ] Integration test: Complex control flow with multiple exits
- [ ] Integration test: Nested scopes with early returns
- [ ] All tests pass (unit + integration)
- [ ] valgrind clean (no memory leaks)
- [ ] Generated C code compiles without warnings

**Test Scenarios:**
1. File RAII pattern with early error returns
2. Buffer allocation with exception-like control flow
3. Lock guard pattern (acquire/release)
4. Multiple resources with complex cleanup ordering
5. Nested loops with break/continue and objects

---

### GitHub Issue Creation Commands

```bash
# Get Epic #5 ID and project field IDs
EPIC_ID=$(gh issue view 37 --json id --jq '.id')
PROJECT_ID="PVT_kwHOBJ7Qkc4BKHLIzg"  # Project #14
FIELD_ID_STATUS="PVTSSF_lAHOBJ7Qkc4BKHLIzg6E1IE"  # Status field

# Create Story #43
gh issue create --repo o2alexanderfedin/cpp-to-c-transpiler \
  --title "Story #43: CFG (Control Flow Graph) Analysis Infrastructure" \
  --label "user story" \
  --body "**Epic:** #37 (Epic #5: RAII + Automatic Destructor Injection)
**Story Points:** 3 SP

**As a** developer
**I want** to analyze control flow graphs to identify all scope exit points
**So that** destructor injection points can be determined accurately

**Acceptance Criteria:**
- [ ] CFG analysis detects all function exit points (return, end of scope)
- [ ] CFG analysis detects control flow statements (goto, break, continue)
- [ ] CFG tracks all local object declarations in scope
- [ ] CFG identifies nested scopes correctly
- [ ] CFG handles multiple return paths
- [ ] Unit tests verify CFG construction for complex functions
- [ ] Integration test: analyze function with early returns

**Technical Notes:**
- Use Clang's CFG API: clang::CFG::buildCFG()
- Iterate CFG blocks to find terminator statements
- Track variable declarations per scope
- Consider using CFGBlock::getTerminator() for exit detection"

# Repeat for Stories #44-49...
# (Use similar pattern for each story)

# Link each story to Epic #5 as sub-issue
# Add each story to Project #14
# Set Status to "Todo"
```

**IMPORTANT:** After creating each story:
1. Link it to Epic #5 using GitHub's sub-issue feature
2. Add it to Project #14
3. Set Status to "Todo"
4. Set Type to "Story" (if Type field exists)

### Output from Prompt 1

**Expected:** 7 user stories created and linked to Epic #5 in GitHub Project #14, all with status "Todo".

---

## Prompt 2: Setup & Planning

### Prerequisites Check

Before starting implementation:

```bash
# 1. All user stories created and linked
gh issue list --repo o2alexanderfedin/cpp-to-c-transpiler \
  --search "is:issue label:\"user story\" Epic #5" \
  --json number,title --jq '. | length'
# Should return: 7

# 2. Project #14 items visible
gh project item-list 14 --owner o2alexanderfedin --limit 100 | \
  jq -r '.items[] | select(.content.title | contains("Story #4")) | .content.number'
# Should list stories #43-49

# 3. Build system ready
cmake -S . -B build && cmake --build build
# Should succeed
```

### Task: Create Implementation Plan

Create a detailed implementation plan in `.prompts/010-execute-epic-5/implementation-plan.md` with:

1. **Execution Order:** Kanban-style selection of next story (based on status)
2. **TDD Workflow:** Red-Green-Refactor for each story
3. **GitHub Integration:** Commands to update story status
4. **Testing Strategy:** Unit tests + integration tests for each story
5. **Validation Checklist:** How to verify each story is complete

### Implementation Plan Template

```markdown
# Epic #5 Implementation Plan

## Execution Strategy

**Kanban Approach:**
1. Query GitHub Project for stories with status="Todo"
2. Select highest priority story (order: #43 → #49)
3. Move story to "In Progress"
4. Execute TDD workflow
5. Move story to "Done"
6. Repeat

## Story Execution Order

1. Story #43: CFG Analysis Infrastructure (FOUNDATION - do first)
2. Story #44: Destructor Injection at Function Exit
3. Story #45: Destructor Injection at Early Returns
4. Story #46: Nested Scope Destruction
5. Story #47: Goto Statement Handling
6. Story #48: Loop Break/Continue Handling
7. Story #49: Integration Testing & Validation (do last)

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
// Modify src/CppToCVisitor.cpp or create new files
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
git commit -m "feat(epic5): implement Story #XX - <title>"

# Update GitHub Project status to "Done"
# (See GitHub integration section)
```

## GitHub Integration Commands

### Update Story Status to "In Progress"

```bash
# Variables
STORY_NUM=43  # Change for each story
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
| #43 | `CFGAnalysisTest.cpp` | CFG construction, exit point detection |
| #44 | `FunctionExitDestructorTest.cpp` | Destructor injection at function end |
| #45 | `EarlyReturnDestructorTest.cpp` | Destructors before early returns |
| #46 | `NestedScopeDestructorTest.cpp` | Nested scope cleanup |
| #47 | `GotoDestructorTest.cpp` | Goto with object cleanup |
| #48 | `LoopDestructorTest.cpp` | Break/continue with destructors |
| #49 | `RAIIIntegrationTest.cpp` | End-to-end RAII scenarios |

### Integration Tests (Story #49)

Real-world RAII scenarios:
1. File handle RAII (open/close)
2. Buffer allocation RAII (malloc/free)
3. Lock guard pattern
4. Complex control flow with multiple resources

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
- [ ] Code follows existing patterns from Epic #4

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
- **Asymmetry**: Try different approaches for different control flow types
- **Dynamics**: Make code adaptable to different CFG patterns
- **Preliminary Action**: Analyze CFG before injecting destructors
```

### Output from Prompt 2

**Expected:** Implementation plan created, GitHub schema queried for option IDs, all commands ready to execute.

---

## Prompt 3: TDD Execution - Story-by-Story Implementation

### Prerequisites

- [ ] Prompt 1 complete: 7 user stories created in GitHub
- [ ] Prompt 2 complete: Implementation plan ready
- [ ] GitHub option IDs obtained (Todo, In Progress, Done)
- [ ] Build system working
- [ ] Git on `develop` branch

### Main Execution Loop

This prompt executes in a loop until all 7 stories are done. For each story:

---

### Step 1: SELECT NEXT STORY (Kanban)

Query GitHub Project for next "Todo" story:

```bash
# Get all stories for Epic #5 with status "Todo"
gh project item-list 14 --owner o2alexanderfedin --format json --limit 100 | \
  jq -r '.items[] | select(.content.number >= 43 and .content.number <= 49) |
         select(.status.name == "Todo") |
         {number: .content.number, title: .content.title}'

# Expected output: First story in "Todo" status
# Select that story number for execution
```

**Decision:** Pick the lowest story number in "Todo" status (following order: #43 → #49).

---

### Step 2: UPDATE STATUS TO "IN PROGRESS"

```bash
# Example for Story #43
STORY_NUM=43
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

**Example for Story #43 (CFG Analysis Infrastructure):**

```cpp
// File: tests/CFGAnalysisTest.cpp

#include "CFGAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Analysis/CFG.h"
#include <iostream>
#include <cassert>

using namespace clang;

// Test 1: CFG detects all return statements
void test_CFGDetectsAllReturns() {
    std::cout << "Running test_CFGDetectsAllReturns... ";

    const char *Code = R"(
        void func(int flag) {
            int x = 10;
            if (flag) {
                return;  // Early return
            }
            int y = 20;
            return;  // Normal return
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Find the function
    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "func") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'func' not found");

    // Build CFG
    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: 2 exit points (2 return statements)
    assert(analyzer.getExitPointCount() == 2);

    std::cout << "✓" << std::endl;
}

// Test 2: CFG tracks local variable declarations
void test_CFGTracksLocalVars() {
    std::cout << "Running test_CFGTracksLocalVars... ";

    const char *Code = R"(
        void func() {
            int x = 10;
            int y = 20;
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    // ... similar setup ...

    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: 2 local variables
    assert(analyzer.getLocalVarCount() == 2);

    std::cout << "✓" << std::endl;
}

// Test 3: CFG identifies nested scopes
void test_CFGIdentifiesNestedScopes() {
    std::cout << "Running test_CFGIdentifiesNestedScopes... ";

    const char *Code = R"(
        void func() {
            int x = 10;
            {
                int y = 20;
            }
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    // ... similar setup ...

    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: 2 scopes (function + nested)
    assert(analyzer.getScopeCount() == 2);

    std::cout << "✓" << std::endl;
}

int main() {
    std::cout << "\n=== CFG Analysis Tests (Story #43) ===\n\n";

    test_CFGDetectsAllReturns();
    test_CFGTracksLocalVars();
    test_CFGIdentifiesNestedScopes();

    std::cout << "\n=== All Tests Passed ===\n";
    return 0;
}
```

**Build and Run (Should FAIL):**

```bash
# Add to CMakeLists.txt
add_executable(CFGAnalysisTest
    tests/CFGAnalysisTest.cpp
    src/CFGAnalyzer.cpp  # Will create this
)
target_compile_definitions(CFGAnalysisTest PRIVATE ${LLVM_DEFINITIONS})
target_include_directories(CFGAnalysisTest PRIVATE ${CMAKE_SOURCE_DIR}/include ${LLVM_INCLUDE_DIRS} ${CLANG_INCLUDE_DIRS})
target_link_libraries(CFGAnalysisTest PRIVATE clangTooling clangFrontend clangAST clangBasic clangAnalysis)

# Build
cmake --build build

# Run (should FAIL because CFGAnalyzer doesn't exist yet)
./build/CFGAnalysisTest
# Expected: Compilation error or assertion failure
```

**RED Phase Complete:** Test exists and fails as expected.

---

### Step 4: TDD GREEN - Implement Minimal Code

Add code to create CFGAnalyzer class.

**Example Implementation for Story #43:**

```cpp
// File: include/CFGAnalyzer.h

#ifndef CFGANALYZER_H
#define CFGANALYZER_H

#include "clang/AST/Decl.h"
#include "clang/Analysis/CFG.h"
#include <memory>
#include <vector>

namespace clang {

class CFGAnalyzer {
public:
    CFGAnalyzer() = default;

    // Analyze CFG for a function
    void analyzeCFG(FunctionDecl *FD);

    // Query methods
    int getExitPointCount() const { return exitPoints.size(); }
    int getLocalVarCount() const { return localVars.size(); }
    int getScopeCount() const { return scopes.size(); }

private:
    std::unique_ptr<CFG> cfg;
    std::vector<CFGBlock*> exitPoints;
    std::vector<VarDecl*> localVars;
    std::vector<CompoundStmt*> scopes;

    void analyzeBlocks();
    void findExitPoints();
    void findLocalVars();
    void findScopes();
};

} // namespace clang

#endif
```

```cpp
// File: src/CFGAnalyzer.cpp

#include "CFGAnalyzer.h"
#include "clang/Analysis/CFG.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/RecursiveASTVisitor.h"

using namespace clang;

void CFGAnalyzer::analyzeCFG(FunctionDecl *FD) {
    // Build CFG
    CFG::BuildOptions options;
    options.AddImplicitDtors = true;
    options.AddInitializers = true;

    cfg = CFG::buildCFG(FD, FD->getBody(), &FD->getASTContext(), options);

    if (!cfg) {
        return;  // CFG construction failed
    }

    // Analyze the CFG
    analyzeBlocks();
    findExitPoints();
    findLocalVars();
    findScopes();
}

void CFGAnalyzer::analyzeBlocks() {
    // Iterate through all CFG blocks
    for (CFG::iterator I = cfg->begin(), E = cfg->end(); I != E; ++I) {
        CFGBlock *Block = *I;
        // Process block...
    }
}

void CFGAnalyzer::findExitPoints() {
    // Find all blocks with return statements
    for (CFG::iterator I = cfg->begin(), E = cfg->end(); I != E; ++I) {
        CFGBlock *Block = *I;
        if (Block->getTerminator().isValid()) {
            if (auto *RS = dyn_cast_or_null<ReturnStmt>(Block->getTerminatorStmt())) {
                exitPoints.push_back(Block);
            }
        }
    }

    // Also add implicit exit (end of function)
    if (cfg->getExit().pred_size() > 0) {
        // Function has implicit return
        // Add exit block if no explicit return
    }
}

void CFGAnalyzer::findLocalVars() {
    // Use RecursiveASTVisitor to find VarDecls
    class VarDeclFinder : public RecursiveASTVisitor<VarDeclFinder> {
    public:
        std::vector<VarDecl*> &vars;
        VarDeclFinder(std::vector<VarDecl*> &v) : vars(v) {}

        bool VisitVarDecl(VarDecl *VD) {
            if (!VD->isLocalVarDecl())
                return true;
            vars.push_back(VD);
            return true;
        }
    };

    // Traverse function body
    // (Implementation continues...)
}

void CFGAnalyzer::findScopes() {
    // Use RecursiveASTVisitor to find CompoundStmts
    class ScopeFinder : public RecursiveASTVisitor<ScopeFinder> {
    public:
        std::vector<CompoundStmt*> &scopes;
        ScopeFinder(std::vector<CompoundStmt*> &s) : scopes(s) {}

        bool VisitCompoundStmt(CompoundStmt *CS) {
            scopes.push_back(CS);
            return true;
        }
    };

    // Traverse function body
    // (Implementation continues...)
}
```

**Build and Run (Should PASS):**

```bash
cmake --build build
./build/CFGAnalysisTest
# Expected: ✓ ✓ ✓ All Tests Passed
```

**GREEN Phase Complete:** Tests pass with minimal implementation.

---

### Step 5: TDD REFACTOR - Apply SOLID/KISS/DRY

Review the code and refactor:

```cpp
// BEFORE (duplication in visitor classes):
class VarDeclFinder : public RecursiveASTVisitor<VarDeclFinder> { ... }
class ScopeFinder : public RecursiveASTVisitor<ScopeFinder> { ... }

// AFTER (single visitor with multiple purposes):
class CFGElementFinder : public RecursiveASTVisitor<CFGElementFinder> {
public:
    std::vector<VarDecl*> &vars;
    std::vector<CompoundStmt*> &scopes;

    CFGElementFinder(std::vector<VarDecl*> &v, std::vector<CompoundStmt*> &s)
        : vars(v), scopes(s) {}

    bool VisitVarDecl(VarDecl *VD) {
        if (VD->isLocalVarDecl())
            vars.push_back(VD);
        return true;
    }

    bool VisitCompoundStmt(CompoundStmt *CS) {
        scopes.push_back(CS);
        return true;
    }
};
```

**SOLID Check:**
- **S**ingle Responsibility: CFGAnalyzer focuses on CFG analysis only ✅
- **O**pen/Closed: Can extend with new analysis methods without modification ✅
- **K**ISS: Simple, clear logic ✅
- **D**RY: No duplication in visitor pattern ✅
- **YAGNI**: Only implement what's needed for CFG analysis ✅

**Run Tests Again:**

```bash
cmake --build build
./build/CFGAnalysisTest
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
./build/CFGAnalysisTest  # New test

# All should pass
```

**Regression Check:** Ensure NO existing tests broke.

---

### Step 7: COMMIT

```bash
git add tests/CFGAnalysisTest.cpp
git add src/CFGAnalyzer.cpp
git add include/CFGAnalyzer.h
git add CMakeLists.txt

git commit -m "feat(epic5): implement CFG analysis infrastructure (Story #43)

- Build CFG using clang::CFG::buildCFG()
- Detect all exit points (return statements)
- Track local variable declarations
- Identify nested scopes (CompoundStmt)
- Add CFGAnalyzer class with query interface
- Unit tests verify CFG construction for complex functions

Refs #43"
```

**Pair Programming Note:** Explain the commit:
- "We used Clang's CFG API to build control flow graph"
- "Exit points are detected by finding return statements in CFG blocks"
- "Local variables and scopes tracked via RecursiveASTVisitor"
- "This provides foundation for destructor injection in next stories"

---

### Step 8: UPDATE STORY STATUS TO "DONE"

```bash
STORY_NUM=43
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

**Verification:** Check GitHub Project UI - Story #43 should show "Done".

---

### Step 9: REPEAT for Next Story

Go back to **Step 1** and select the next "Todo" story.

Continue loop until all 7 stories (#43-#49) are "Done".

---

## Final Steps: Epic Completion

After all 7 stories are done:

### 1. Update Epic #5 Status to "Done"

```bash
EPIC_NUM=37

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
git tag -a v0.3.0 -m "Release v0.3.0: RAII + Automatic Destructor Injection (Epic #5)

Epic #5 Complete - RAII + Automatic Destructor Injection

Features:
- CFG (Control Flow Graph) analysis infrastructure (Story #43)
- Destructor injection at function exit (Story #44)
- Destructor injection at early returns (Story #45)
- Nested scope destruction (Story #46)
- Goto statement handling (Story #47)
- Loop break/continue handling (Story #48)
- Comprehensive RAII integration tests (Story #49)

Story Points Delivered: 13 SP
Tests Added: 40+ unit tests, 5 integration tests
All tests passing, zero regressions

Deliverables:
✅ CFG analysis detects all exit points
✅ Destructors automatically injected at scope exits
✅ Destruction in reverse construction order
✅ Complex control flow handled (goto, break, continue)
✅ valgrind clean (no memory leaks)
✅ Real-world RAII patterns working (File, Buffer, Lock)

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>"

# Push tag
git push origin v0.3.0
```

### 3. Create GitHub Release

```bash
gh release create v0.3.0 \
  --title "v0.3.0: RAII + Automatic Destructor Injection (Epic #5)" \
  --notes "Epic #5 Complete - RAII + Automatic Destructor Injection

## Features Delivered

- ✅ CFG analysis infrastructure (Story #43)
- ✅ Destructor injection at function exit (Story #44)
- ✅ Destructor injection at early returns (Story #45)
- ✅ Nested scope destruction (Story #46)
- ✅ Goto statement handling (Story #47)
- ✅ Loop break/continue handling (Story #48)
- ✅ Integration testing & validation (Story #49)

## Metrics

- **Story Points:** 13 SP delivered
- **Tests:** 40+ unit tests, 5 integration tests
- **Test Coverage:** Maintained 1.29:1 test-to-production ratio
- **Quality:** Zero regressions, all tests passing

## Example

\`\`\`cpp
// C++ Input (RAII pattern)
void processFile(const char* filename) {
    File f(filename);  // Constructor: acquires file handle
    Buffer buf(1024);  // Constructor: allocates memory

    if (f.hasError()) {
        return;  // Early return: must destroy buf, then f
    }

    buf.fill(f);
    // Normal exit: destroy buf, then f (reverse order)
}
\`\`\`

\`\`\`c
// Generated C Output
void processFile(const char* filename) {
    struct File f;
    File__ctor(&f, filename);

    struct Buffer buf;
    Buffer__ctor(&buf, 1024);

    if (File_hasError(&f)) {
        Buffer__dtor(&buf);  // Injected: destroy buf first
        File__dtor(&f);      // Injected: destroy f second
        return;
    }

    Buffer_fill(&buf, &f);

    Buffer__dtor(&buf);  // Injected: destroy buf first
    File__dtor(&f);      // Injected: destroy f second
}
\`\`\`

## Next Steps

Epic #6: Single Inheritance Support (Weeks 7-8)

🤖 Generated with [Claude Code](https://claude.com/claude-code)"
```

### 4. Close Epic #5 Issue

```bash
gh issue close 37 --comment "Epic #5 Complete ✅

All 7 user stories delivered:
- Story #43: CFG Analysis Infrastructure ✅
- Story #44: Destructor Injection at Function Exit ✅
- Story #45: Destructor Injection at Early Returns ✅
- Story #46: Nested Scope Destruction ✅
- Story #47: Goto Statement Handling ✅
- Story #48: Loop Break/Continue Handling ✅
- Story #49: Integration Testing & Validation ✅

**Total Story Points:** 13 SP
**Duration:** <actual time taken>
**Tests:** 40+ unit tests, 5 integration tests
**Quality:** Zero regressions, all tests passing, valgrind clean

Release: v0.3.0

🤖 Generated with [Claude Code](https://claude.com/claude-code)"
```

### 5. Update EPICS.md and ARCHITECTURE.md

```bash
# Update EPICS.md to mark Epic #5 as complete
# Update ARCHITECTURE.md if design evolved

git add EPICS.md docs/ARCHITECTURE.md
git commit -m "docs: update EPICS.md and ARCHITECTURE.md after Epic #5 completion"
git push origin develop
```

---

## Success Criteria for Meta-Prompt Completion

- [ ] All 7 user stories created in GitHub
- [ ] All stories linked to Epic #5 as sub-issues
- [ ] All stories moved through Kanban flow: Todo → In Progress → Done
- [ ] TDD followed for every story (RED-GREEN-REFACTOR)
- [ ] All tests passing (40+ new tests, all existing tests still pass)
- [ ] Zero regressions
- [ ] SOLID, KISS, DRY, YAGNI principles applied
- [ ] Conventional commits for every story
- [ ] Epic #5 status = "Done" in GitHub Project
- [ ] Release v0.3.0 created
- [ ] Epic #5 issue closed
- [ ] Documentation updated
- [ ] valgrind clean (no memory leaks)

---

## Troubleshooting

### Issue: CFG construction fails

**Solution:** Check that function has a body:

```cpp
if (!FD->hasBody()) {
    // Function declaration only, no definition
    return;
}

Stmt *Body = FD->getBody();
if (!Body) {
    return;
}
```

### Issue: Destructor injection duplicates destructors

**Solution:** Track which objects have been destroyed:

```cpp
std::set<VarDecl*> destroyedObjects;

void injectDestructor(VarDecl *VD) {
    if (destroyedObjects.count(VD)) {
        return;  // Already destroyed
    }
    // ... inject destructor call ...
    destroyedObjects.insert(VD);
}
```

### Issue: Destruction order incorrect

**Solution:** Use stack or reverse iteration:

```cpp
std::vector<VarDecl*> constructionOrder;  // Fill during analysis

// Inject destructors in reverse order
for (auto it = constructionOrder.rbegin(); it != constructionOrder.rend(); ++it) {
    injectDestructor(*it);
}
```

---

## Pair Programming Prompts

Throughout execution, act as pair programming partner:

**Navigator Role (you):**
- "Let's start with CFG analysis to understand control flow"
- "I think we need to track construction order in a vector"
- "Wait, this could duplicate destructor calls - let's add a guard"
- "Have we verified the destruction order is actually reversed?"

**Driver Role (implementation):**
- Write the code based on navigator guidance
- Ask questions: "Should we handle implicit destructors?"
- Propose refactorings: "This method is getting long, should we split it?"

**Switch roles every 15-20 minutes** (conceptually).

---

## Velocity Tracking

After Epic #5 completion, update velocity metrics:

```bash
# Calculate story points per hour
STORY_POINTS=13
HOURS=<actual time taken>
VELOCITY=$(echo "scale=2; $STORY_POINTS / $HOURS" | bc)

echo "Epic #5 Velocity: $VELOCITY SP/hour"

# Compare with Epic #19 velocity (8.89 SP/hour)
# Expected: Similar velocity (Epic #5 is moderate complexity)
```

**Target Velocity:** 6-9 SP/hour (based on Epic #19 baseline of 8.89 SP/hour)

---

## References

- Epic #5 Issue: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/37
- Clang CFG Docs: https://clang.llvm.org/doxygen/classclang_1_1CFG.html
- ARCHITECTURE.md: RAII section
- PNaCl Exception Handling (reference): https://www.chromium.org/nativeclient/pnacl/exception-handling/

---

**Created:** 2025-12-08
**Meta-Prompt Type:** TDD Execution with GitHub Integration
**Methodology:** Red-Green-Refactor + Kanban + Pair Programming

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
