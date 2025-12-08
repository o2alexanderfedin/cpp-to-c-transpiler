# Meta-Prompt: Execute Epic #19 - Header File Generation & Separation

## Context

Epic #19 has been fully designed and broken down into 6 User Stories in GitHub Project #14. This meta-prompt provides a systematic approach to implement all stories using TDD, pair programming principles, and SOLID design.

**Epic #19:** Header File Generation & Separation (Issue #136)
**User Stories:** #137-142 (8 Story Points total)
**Phase:** 2.5 (Weeks 12.5-13.5)

## Core Principles

### Source of Truth
- **GitHub Project #14** is the ONLY source of truth for epic and story status
- **NEVER** assume a story is complete without checking GitHub
- **ALWAYS** update GitHub status immediately when starting or completing work

### Development Methodology
1. **TDD (Test-Driven Development)**: Red → Green → Refactor cycle for ALL code
2. **Pair Programming**: Think aloud, explain reasoning, review as you go
3. **SOLID Principles**: Single Responsibility, Open/Closed, Liskov Substitution, Interface Segregation, Dependency Inversion
4. **KISS**: Keep It Simple, Stupid - prefer simple solutions
5. **DRY**: Don't Repeat Yourself - extract common functionality
6. **YAGNI**: You Aren't Gonna Need It - don't build unused features
7. **TRIZ**: Use systematic innovation and contradiction resolution
8. **Emergent Design**: Let design evolve from tests and requirements

### Kanban Workflow
1. Check GitHub Project #14 for next available story (Status = "Ready" or "Todo")
2. Move story to "In Progress" BEFORE starting work
3. Implement using TDD cycle
4. Move story to "Done" IMMEDIATELY after completion
5. Repeat until Epic #19 complete

## Meta-Prompt Structure

This meta-prompt creates a **single master prompt** that will be executed iteratively to complete Epic #19. The master prompt is self-contained and stateless, pulling current state from GitHub on each execution.

---

## Master Prompt: Epic #19 Implementation Agent

**Objective:** Systematically implement all User Stories in Epic #19 using TDD, SOLID principles, and GitHub Project #14 as source of truth.

### Execution Protocol

**On Each Invocation:**

1. **Fetch Current State from GitHub Project #14**
   ```bash
   # Get all items in Project #14 related to Epic #19
   gh project item-list 14 --owner o2alexanderfedin --format json --limit 1000 > /tmp/project_state.json

   # Extract Epic #19 status
   EPIC_STATUS=$(jq -r '.items[] | select(.content.number == 136) | .status' /tmp/project_state.json)

   # Extract all User Stories for Epic #19 (#137-142)
   jq '.items[] | select(.content.number >= 137 and .content.number <= 142) | {number: .content.number, title: .title, status: .status, type: .type}' /tmp/project_state.json > /tmp/epic19_stories.json
   ```

2. **Determine Next Action** (Kanban Pull System)
   - If Epic status != "In Progress": Update to "In Progress"
   - Find first story with status = "Todo" or "Ready"
   - If no stories in "Todo"/"Ready": Check for "In Progress" stories (resume work)
   - If all stories "Done": Mark Epic as "Done" and exit

3. **Execute TDD Cycle for Selected Story**
   - Update story status to "In Progress" in GitHub
   - Read story acceptance criteria from GitHub Issue
   - Implement using TDD: Write Test → Fail → Implement → Pass → Refactor
   - Run all tests + linters
   - Update story status to "Done" in GitHub
   - Commit changes with reference to story number

4. **Loop** until Epic complete

---

## Detailed Implementation Guide

### Phase 1: Epic Initialization

**First Invocation Tasks:**

1. **Update Epic #19 Status to "In Progress"**
   ```bash
   # Get Epic item ID
   EPIC_ITEM_ID=$(jq -r '.items[] | select(.content.number == 136) | .id' /tmp/project_state.json)

   # Get "In Progress" status field ID (from project schema)
   # Status field options: Todo, In Progress, Done
   # Need to update via GraphQL

   gh api graphql -f query='
   mutation {
     updateProjectV2ItemFieldValue(input: {
       projectId: "PVT_kwHOBJ7Qkc4BKHLI"
       itemId: "'$EPIC_ITEM_ID'"
       fieldId: "PVTSSF_lAHOBJ7Qkc4BKHLIzgRfDKc"
       value: {singleSelectOptionId: "47fc9ee4"}
     }) {
       projectV2Item { id }
     }
   }'
   ```

2. **Display Epic Overview**
   ```
   ╔══════════════════════════════════════════════════════════════╗
   ║  Epic #19: Header File Generation & Separation              ║
   ╠══════════════════════════════════════════════════════════════╣
   ║  Status: In Progress                                         ║
   ║  Stories: 6 total (8 Story Points)                           ║
   ║  Phase: 2.5 (Weeks 12.5-13.5)                                ║
   ╚══════════════════════════════════════════════════════════════╝

   User Stories:
   ┌──────┬────────────────────────────────────────┬────────┬─────────┐
   │ #    │ Title                                  │ SP     │ Status  │
   ├──────┼────────────────────────────────────────┼────────┼─────────┤
   │ #137 │ Header/Implementation Separation       │ 2      │ Todo    │
   │ #138 │ Include Guard Generation               │ 1      │ Todo    │
   │ #139 │ Forward Declaration Support            │ 2      │ Todo    │
   │ #140 │ Dependency Tracking                    │ 1      │ Todo    │
   │ #141 │ File Output System                     │ 1      │ Todo    │
   │ #142 │ Integration Testing                    │ 1      │ Todo    │
   └──────┴────────────────────────────────────────┴────────┴─────────┘
   ```

3. **Select First Story** (Kanban Pull)
   - Story #137 is first in sequence
   - Check status = "Todo"
   - Pull into "In Progress"

### Phase 2: Story Implementation (TDD Cycle)

**Template for Each Story:**

#### Step 1: Fetch Story Details

```bash
# Get story body (acceptance criteria, technical details)
gh issue view 137 --repo o2alexanderfedin/cpp-to-c-transpiler --json body,title,labels > /tmp/story137.json

# Parse acceptance criteria
jq -r '.body' /tmp/story137.json | grep -A 100 "## Acceptance Criteria" | grep -B 100 "## Technical Details"
```

#### Step 2: Update Story Status to "In Progress"

```bash
# Get story item ID from project
STORY_ITEM_ID=$(jq -r '.items[] | select(.content.number == 137) | .id' /tmp/project_state.json)

# Update to "In Progress"
gh api graphql -f query='
mutation {
  updateProjectV2ItemFieldValue(input: {
    projectId: "PVT_kwHOBJ7Qkc4BKHLI"
    itemId: "'$STORY_ITEM_ID'"
    fieldId: "PVTSSF_lAHOBJ7Qkc4BKHLIzgRfDKc"
    value: {singleSelectOptionId: "47fc9ee4"}
  }) {
    projectV2Item { id }
  }
}'

echo "✓ Story #137 status updated to 'In Progress'"
```

#### Step 3: TDD Cycle - Red Phase (Write Failing Test)

**Pair Programming Narrative:**

```
I'm now working on Story #137: Header/Implementation Separation.

Let me think through what we need to test first. According to the acceptance criteria:
- HeaderSeparator class analyzes Decl nodes
- RecordDecl (complete definitions) routed to header
- FunctionDecl declarations routed to header
- FunctionDecl definitions routed to implementation

SOLID Principle (Single Responsibility): HeaderSeparator should do ONE thing - route declarations to appropriate outputs.

Let me start with the simplest test case: routing a complete struct definition to the header list.

Here's my test (following TDD - write test FIRST):
```

```cpp
// tests/HeaderSeparatorTest.cpp
#include "HeaderSeparator.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>

// Test 1: Simple struct routes to header
TEST(HeaderSeparatorTest, CompleteStructGoesToHeader) {
    // Arrange
    const char *Code = R"(
        struct Point {
            int x;
            int y;
        };
    )";

    // Act
    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // Assert
    EXPECT_EQ(separator.getHeaderDecls().size(), 1);
    EXPECT_EQ(separator.getImplDecls().size(), 0);

    auto *FirstDecl = separator.getHeaderDecls()[0];
    EXPECT_TRUE(llvm::isa<clang::RecordDecl>(FirstDecl));
    EXPECT_EQ(llvm::cast<clang::RecordDecl>(FirstDecl)->getName(), "Point");
}
```

**Explanation (Pair Programming):**
- I'm testing the BEHAVIOR, not implementation details
- Test is SIMPLE (KISS principle)
- Test will FAIL because HeaderSeparator doesn't exist yet (Red phase)
- This defines the API we want: `analyzeTranslationUnit()`, `getHeaderDecls()`, `getImplDecls()`

#### Step 4: TDD Cycle - Green Phase (Minimal Implementation)

```
Now let's write the MINIMUM code to make this test pass.

YAGNI principle: Only implement what's needed for THIS test.
```

```cpp
// include/HeaderSeparator.h
#ifndef HEADER_SEPARATOR_H
#define HEADER_SEPARATOR_H

#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <vector>

// SOLID: Single Responsibility - only separates headers from impl
class HeaderSeparator : public clang::RecursiveASTVisitor<HeaderSeparator> {
public:
    // Analyze entire translation unit
    void analyzeTranslationUnit(clang::TranslationUnitDecl *TU);

    // Access results
    const std::vector<clang::Decl*>& getHeaderDecls() const { return headerDecls; }
    const std::vector<clang::Decl*>& getImplDecls() const { return implDecls; }

    // Visitor methods (called by RecursiveASTVisitor)
    bool VisitRecordDecl(clang::RecordDecl *D);

private:
    std::vector<clang::Decl*> headerDecls;
    std::vector<clang::Decl*> implDecls;
};

#endif
```

```cpp
// src/HeaderSeparator.cpp
#include "HeaderSeparator.h"

void HeaderSeparator::analyzeTranslationUnit(clang::TranslationUnitDecl *TU) {
    // KISS: Just traverse the AST
    TraverseDecl(TU);
}

bool HeaderSeparator::VisitRecordDecl(clang::RecordDecl *D) {
    // YAGNI: Only handle complete definitions for now
    if (D->isCompleteDefinition()) {
        headerDecls.push_back(D);
    }
    return true;  // Continue traversal
}
```

**Run Test:**
```bash
cd build
cmake --build . --target HeaderSeparatorTest
./tests/HeaderSeparatorTest --gtest_filter=HeaderSeparatorTest.CompleteStructGoesToHeader

# Expected: PASS (Green phase achieved)
```

#### Step 5: TDD Cycle - Next Test (Function Declaration)

```
Test passes! Now let's add the next test case.

According to acceptance criteria, function declarations (without body) should go to header.
```

```cpp
TEST(HeaderSeparatorTest, FunctionDeclarationGoesToHeader) {
    const char *Code = R"(
        void myFunction(int x);
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    EXPECT_EQ(separator.getHeaderDecls().size(), 1);
    EXPECT_EQ(separator.getImplDecls().size(), 0);

    auto *FirstDecl = separator.getHeaderDecls()[0];
    EXPECT_TRUE(llvm::isa<clang::FunctionDecl>(FirstDecl));
}
```

**Implement:**
```cpp
// Add to HeaderSeparator.h
bool VisitFunctionDecl(clang::FunctionDecl *D);

// Add to HeaderSeparator.cpp
bool HeaderSeparator::VisitFunctionDecl(clang::FunctionDecl *D) {
    if (!D->hasBody()) {
        // Declaration only → header
        headerDecls.push_back(D);
    }
    // Note: Definitions handled in next test
    return true;
}
```

#### Step 6: TDD Cycle - Function Definition (Goes to BOTH)

```
Now the complex case: function definitions go to IMPLEMENTATION, but we also need a DECLARATION in the header.

This is where SOLID comes in - we need to create a declaration-only version.
```

```cpp
TEST(HeaderSeparatorTest, FunctionDefinitionGoesToImplWithDeclInHeader) {
    const char *Code = R"(
        void myFunction(int x) {
            // function body
        }
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // Definition goes to impl
    EXPECT_EQ(separator.getImplDecls().size(), 1);

    // Declaration goes to header
    EXPECT_EQ(separator.getHeaderDecls().size(), 1);

    // Header version should be declaration-only
    auto *HeaderDecl = llvm::cast<clang::FunctionDecl>(separator.getHeaderDecls()[0]);
    EXPECT_FALSE(HeaderDecl->hasBody());
}
```

**Implementation Challenge:**
We need to create a declaration-only FunctionDecl from a definition. This requires using Clang's AST node creation.

```cpp
// HeaderSeparator.cpp - updated
#include "CNodeBuilder.h"  // Reuse existing helper from Epic #2

bool HeaderSeparator::VisitFunctionDecl(clang::FunctionDecl *D) {
    if (D->hasBody()) {
        // Definition → implementation
        implDecls.push_back(D);

        // Also create declaration for header
        // SOLID: Use dependency injection - CNodeBuilder creates nodes
        CNodeBuilder builder(D->getASTContext());
        auto *DeclOnly = builder.createFunctionDeclOnly(D);
        headerDecls.push_back(DeclOnly);
    } else {
        // Declaration only → header
        headerDecls.push_back(D);
    }
    return true;
}
```

**Add to CNodeBuilder** (if not exists):
```cpp
// CNodeBuilder.h
clang::FunctionDecl* createFunctionDeclOnly(clang::FunctionDecl *FD);

// CNodeBuilder.cpp
clang::FunctionDecl* CNodeBuilder::createFunctionDeclOnly(clang::FunctionDecl *FD) {
    // DRY: Reuse existing logic, just don't include body
    // Create FunctionDecl with same signature but no body
    // (Implementation details using Clang APIs)
    // ...
}
```

#### Step 7: Refactor Phase

```
All tests pass! Time to refactor.

Look for:
- Duplicate code (DRY violation)
- Complex methods (KISS violation)
- Multiple responsibilities (SOLID violation)
```

**Refactoring Example:**
```cpp
// Before: Duplication in routing logic
if (D->hasBody()) {
    implDecls.push_back(D);
    // ... create decl ...
    headerDecls.push_back(DeclOnly);
} else {
    headerDecls.push_back(D);
}

// After: Extract method (DRY)
void HeaderSeparator::routeFunctionDecl(clang::FunctionDecl *D) {
    if (D->hasBody()) {
        routeDefinition(D);
    } else {
        routeDeclaration(D);
    }
}

void HeaderSeparator::routeDefinition(clang::FunctionDecl *D) {
    implDecls.push_back(D);

    CNodeBuilder builder(D->getASTContext());
    headerDecls.push_back(builder.createFunctionDeclOnly(D));
}

void HeaderSeparator::routeDeclaration(clang::Decl *D) {
    headerDecls.push_back(D);
}
```

**Run ALL Tests + Linters:**
```bash
# Run all tests
./tests/HeaderSeparatorTest

# Run clang-tidy (linter)
clang-tidy src/HeaderSeparator.cpp -- -I include

# Run clang-format (style check)
clang-format -i src/HeaderSeparator.cpp include/HeaderSeparator.h

# Run type checker (tsc equivalent for C++)
# In C++, this is compile-time type checking (already done)
```

#### Step 8: Complete All Acceptance Criteria

**Repeat TDD cycle** for each acceptance criterion:

1. ✓ RecordDecl (complete definitions) routed to header
2. ✓ FunctionDecl declarations routed to header
3. ✓ FunctionDecl definitions routed to implementation
4. Test Case 4: Maintains separate lists (already tested)
5. Test Case 5: Integration with CppToCVisitor
6. Test Case 6: Unit tests for routing logic (all written above)

**Integration Test:**
```cpp
TEST(HeaderSeparatorTest, IntegrationWithComplexClass) {
    const char *Code = R"(
        class MyClass {
            int x;
        public:
            MyClass(int x);
            int getX() const;
        };

        MyClass::MyClass(int x) : x(x) {}
        int MyClass::getX() const { return x; }
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // Header should have: struct MyClass + 2 declarations
    EXPECT_EQ(separator.getHeaderDecls().size(), 3);

    // Impl should have: 2 definitions (ctor + getX)
    EXPECT_EQ(separator.getImplDecls().size(), 2);
}
```

#### Step 9: Commit and Update Story Status

```bash
# Run full test suite
cmake --build . --target test

# Run linters
./scripts/run_linters.sh

# Commit with story reference
git add src/HeaderSeparator.cpp include/HeaderSeparator.h tests/HeaderSeparatorTest.cpp
git commit -m "feat(epic19): implement header/impl separation (Story #137)

- Add HeaderSeparator class with RecursiveASTVisitor
- Route RecordDecl complete definitions to header
- Route FunctionDecl declarations to header
- Route FunctionDecl definitions to impl (+ create decl for header)
- 6+ unit tests covering all acceptance criteria
- Integration with CNodeBuilder for decl creation

Story Points: 2
Tests: All passing
Linters: Clean

Closes #137"

# Push to GitHub
git push origin develop
```

#### Step 10: Update Story Status to "Done"

```bash
# Get story item ID
STORY_ITEM_ID=$(jq -r '.items[] | select(.content.number == 137) | .id' /tmp/project_state.json)

# Update to "Done"
gh api graphql -f query='
mutation {
  updateProjectV2ItemFieldValue(input: {
    projectId: "PVT_kwHOBJ7Qkc4BKHLI"
    itemId: "'$STORY_ITEM_ID'"
    fieldId: "PVTSSF_lAHOBJ7Qkc4BKHLIzgRfDKc"
    value: {singleSelectOptionId: "98236657"}
  }) {
    projectV2Item { id }
  }
}'

echo "✓ Story #137 marked as DONE in GitHub Project #14"

# Close issue
gh issue close 137 --repo o2alexanderfedin/cpp-to-c-transpiler --comment "Completed via commit [SHA]. All acceptance criteria met, tests passing, linters clean."
```

### Phase 3: Repeat for All Stories

**Story #138: Include Guard Generation** (1 SP)
- Follow same TDD cycle
- Test: generateGuardName("Point.h") → "POINT_H"
- Test: emitGuardBegin() writes correct #ifndef/#define
- Test: emitGuardEnd() writes correct #endif
- Refactor: Extract character replacement logic
- Commit: "feat(epic19): implement include guard generation (Story #138)"
- Update status: Done

**Story #139: Forward Declaration Support** (2 SP)
- TDD: Test detecting pointer to incomplete type
- TDD: Test emitting forward declaration
- TDD: Test circular dependencies (A→B, B→A)
- TDD: Test avoiding duplicate forward decls
- Refactor: Extract dependency graph analysis
- Commit: "feat(epic19): implement forward declaration support (Story #139)"
- Update status: Done

**Story #140: Dependency Tracking** (1 SP)
- TDD: Test tracking own header include
- TDD: Test detecting runtime library usage (future-proof)
- TDD: Test generating include directives in order
- Refactor: Use dependency injection for extensibility
- Commit: "feat(epic19): implement dependency tracking (Story #140)"
- Update status: Done

**Story #141: File Output System** (1 SP)
- TDD: Test command-line option parsing
- TDD: Test file creation with default names
- TDD: Test file creation with custom names
- TDD: Test error handling (permissions, disk full)
- Refactor: Extract file I/O into separate class
- Commit: "feat(epic19): implement file output system (Story #141)"
- Update status: Done

**Story #142: Integration Testing** (1 SP)
- Create integration test script
- Test: Full .h/.c generation from C++ class
- Test: Compile .h standalone (gcc -c)
- Test: Compile .c with .h (gcc -c)
- Test: Multiple inclusion safety
- Test: Forward declarations compile
- Commit: "feat(epic19): add integration tests (Story #142)"
- Update status: Done

### Phase 4: Epic Completion

**After All Stories Done:**

1. **Verify All Stories Complete**
   ```bash
   gh project item-list 14 --owner o2alexanderfedin --format json --limit 1000 | \
     jq '.items[] | select(.content.number >= 137 and .content.number <= 142) | {number: .content.number, status: .status}'

   # Expected: All status = "Done"
   ```

2. **Run Full Test Suite**
   ```bash
   cmake --build . --target test
   # Expected: All tests pass

   ./scripts/run_linters.sh
   # Expected: No warnings/errors
   ```

3. **Update Epic #19 Status to "Done"**
   ```bash
   EPIC_ITEM_ID=$(jq -r '.items[] | select(.content.number == 136) | .id' /tmp/project_state.json)

   gh api graphql -f query='
   mutation {
     updateProjectV2ItemFieldValue(input: {
       projectId: "PVT_kwHOBJ7Qkc4BKHLI"
       itemId: "'$EPIC_ITEM_ID'"
       fieldId: "PVTSSF_lAHOBJ7Qkc4BKHLIzgRfDKc"
       value: {singleSelectOptionId: "98236657"}
     }) {
       projectV2Item { id }
     }
   }'
   ```

4. **Close Epic Issue**
   ```bash
   gh issue close 136 --repo o2alexanderfedin/cpp-to-c-transpiler --comment "Epic #19 complete! All 6 user stories implemented and tested.

   Summary:
   - ✅ Story #137: Header/Implementation Separation (2 SP)
   - ✅ Story #138: Include Guard Generation (1 SP)
   - ✅ Story #139: Forward Declaration Support (2 SP)
   - ✅ Story #140: Dependency Tracking (1 SP)
   - ✅ Story #141: File Output System (1 SP)
   - ✅ Story #142: Integration Testing (1 SP)

   Total: 8 Story Points delivered
   Tests: All passing
   Linters: Clean
   Integration: Verified

   Phase 2.5 complete! Ready for Phase 3 (Virtual Functions)."
   ```

5. **Create Release Tag**
   ```bash
   git tag -a v0.3.0 -m "Release v0.3.0: Epic #19 - Header File Generation

   Phase 2.5 Complete - Header file support implemented

   Features:
   - Separate .h/.c file generation
   - Include guard generation
   - Forward declaration support
   - Dependency tracking
   - File output system with command-line options
   - Comprehensive integration tests

   Components Added:
   - HeaderSeparator (150-200 LOC)
   - IncludeGuardGenerator (50-80 LOC)
   - DependencyAnalyzer (100-150 LOC)
   - CodeGenerator dual-stream updates (100-150 LOC)
   - File I/O system (80-120 LOC)

   Total LOC: ~500-700
   Tests: 25+ unit tests, 6 integration tests
   Coverage: 95%+

   Closes #136"

   git push origin v0.3.0
   ```

---

## Execution Checklist

**Before Each Story:**
- [ ] Fetch latest GitHub Project #14 state
- [ ] Identify next story in Kanban queue
- [ ] Update story status to "In Progress"
- [ ] Read acceptance criteria from GitHub Issue

**During Story Implementation:**
- [ ] Follow TDD: Write test → Fail → Implement → Pass → Refactor
- [ ] Apply SOLID principles at every step
- [ ] Keep code SIMPLE (KISS)
- [ ] Avoid duplication (DRY)
- [ ] Only implement what's needed (YAGNI)
- [ ] Think aloud (Pair Programming narrative)
- [ ] Run tests + linters after each change

**After Story Complete:**
- [ ] All acceptance criteria met
- [ ] All tests passing (unit + integration)
- [ ] Linters clean (no warnings)
- [ ] Code reviewed (explain reasoning)
- [ ] Commit with story reference
- [ ] Push to GitHub
- [ ] Update story status to "Done" in GitHub Project
- [ ] Close story issue with completion comment

**After Epic Complete:**
- [ ] All stories status = "Done"
- [ ] Full test suite passing
- [ ] Linters clean
- [ ] Integration tests passing
- [ ] Update epic status to "Done"
- [ ] Close epic issue
- [ ] Create release tag
- [ ] Update documentation

---

## GitHub API Reference

**Get Project Items:**
```bash
gh project item-list 14 --owner o2alexanderfedin --format json --limit 1000
```

**Update Item Status (GraphQL):**
```graphql
mutation {
  updateProjectV2ItemFieldValue(input: {
    projectId: "PVT_kwHOBJ7Qkc4BKHLI"
    itemId: "<ITEM_ID>"
    fieldId: "PVTSSF_lAHOBJ7Qkc4BKHLIzgRfDKc"
    value: {singleSelectOptionId: "<STATUS_OPTION_ID>"}
  }) {
    projectV2Item { id }
  }
}
```

**Status Option IDs:**
- Todo: (need to query)
- In Progress: "47fc9ee4"
- Done: "98236657"

**Get Issue Details:**
```bash
gh issue view <NUMBER> --repo o2alexanderfedin/cpp-to-c-transpiler --json body,title,labels
```

**Close Issue:**
```bash
gh issue close <NUMBER> --repo o2alexanderfedin/cpp-to-c-transpiler --comment "Completion message"
```

---

## TDD Examples for Each Story

### Story #137: Header/Implementation Separation

**Test Sequence:**
1. Test: Empty TU → empty lists
2. Test: Simple struct → header list
3. Test: Function decl → header list
4. Test: Function def → impl list + decl in header
5. Test: Class with methods → struct in header, methods in impl
6. Test: Integration with complex class

### Story #138: Include Guard Generation

**Test Sequence:**
1. Test: "Point.h" → "POINT_H"
2. Test: "my-class.h" → "MY_CLASS_H"
3. Test: Special chars replaced
4. Test: emitGuardBegin() output correct
5. Test: emitGuardEnd() output correct
6. Test: Full guard wrapping content

### Story #139: Forward Declaration Support

**Test Sequence:**
1. Test: Detect pointer to incomplete type
2. Test: Emit forward decl before usage
3. Test: Circular deps (A→B, B→A)
4. Test: No duplicate forward decls
5. Test: Non-pointer fields ignored
6. Test: Pointer to primitive ignored

### Story #140: Dependency Tracking

**Test Sequence:**
1. Test: Own header included first
2. Test: Runtime lib detected (future)
3. Test: Include order correct
4. Test: No redundant includes
5. Test: Extensible architecture

### Story #141: File Output System

**Test Sequence:**
1. Test: Parse --output-header option
2. Test: Parse --output-impl option
3. Test: Default names from input
4. Test: File creation succeeds
5. Test: Error handling (permissions)
6. Test: Help text displays options

### Story #142: Integration Testing

**Test Sequence:**
1. Test: Generate .h/.c from C++ class
2. Test: gcc -c header.h succeeds
3. Test: gcc -c impl.c succeeds
4. Test: Multiple inclusion safe
5. Test: Forward decls compile
6. Test: Full program links and runs

---

## Emergent Design Principles

**Let Tests Drive Design:**
- Don't design classes upfront
- Write test for desired behavior
- Implement minimal code to pass
- Refactor when patterns emerge

**Recognize Patterns:**
- If routing logic gets complex → Extract strategy pattern
- If multiple file types → Abstract file writer interface
- If dependency tracking grows → Graph-based analyzer

**TRIZ Contradiction Resolution:**
- **Contradiction**: Need flexibility (many output formats) vs. simplicity (single responsibility)
- **Resolution**: Use Strategy pattern (swap file writers) with simple interface
- **Result**: Flexible yet simple design

---

## Success Metrics

**Story-Level:**
- All acceptance criteria met ✓
- Tests passing ✓
- Linters clean ✓
- Committed with story reference ✓
- GitHub status updated ✓

**Epic-Level:**
- All 6 stories complete ✓
- 8 story points delivered ✓
- Full test suite passing ✓
- Integration tests passing ✓
- Release tag created ✓

---

## Failure Recovery

**If Test Fails:**
1. Don't proceed to next test
2. Fix failing test first
3. Re-run all tests
4. Only move forward when green

**If Linter Reports Issues:**
1. Fix all warnings/errors
2. Don't commit with linter issues
3. Run linter again
4. Only commit when clean

**If GitHub Update Fails:**
1. Check network connection
2. Verify project/item IDs correct
3. Retry with exponential backoff
4. Log error and continue (manual update later)

---

**Meta-Prompt Version:** 1.0
**Created:** $(date +%Y-%m-%d)
**Epic:** #19 - Header File Generation & Separation
**Status:** Ready for Execution
