# Epic #5 Implementation Plan

**Created:** 2025-12-08
**Epic:** #37 (RAII + Automatic Destructor Injection)
**Total Story Points:** 13 SP
**Estimated Duration:** 2 weeks

---

## Execution Strategy

**Kanban Approach:**
1. Query GitHub Project for stories with status="Todo"
2. Select highest priority story (order: #151 → #157)
3. Move story to "In Progress"
4. Execute TDD workflow (RED-GREEN-REFACTOR)
5. Move story to "Done"
6. Repeat

**GitHub Project Details:**
- **Project ID:** PVT_kwHOBJ7Qkc4BKHLI
- **Status Field ID:** PVTSSF_lAHOBJ7Qkc4BKHLIzg6E1IE
- **Todo Option ID:** f75ad846
- **In Progress Option ID:** 47fc9ee4
- **Done Option ID:** 98236657

---

## Story Execution Order

1. **Story #151:** CFG Analysis Infrastructure (3 SP) - FOUNDATION - do first
2. **Story #152:** Destructor Injection at Function Exit (2 SP)
3. **Story #153:** Destructor Injection at Early Returns (2 SP)
4. **Story #154:** Nested Scope Destruction (2 SP)
5. **Story #155:** Goto Statement Handling (1 SP)
6. **Story #156:** Loop Break/Continue Handling (1 SP)
7. **Story #157:** Integration Testing & Validation (2 SP) - do last

---

## TDD Workflow Per Story

### Step 1: RED - Write Failing Test

```bash
# Create test file: tests/StoryXXXTest.cpp
# Write test that captures acceptance criteria
# Build should succeed, test should FAIL
cmake --build build
./build/StoryXXXTest  # Should fail
```

**Example for Story #151 (CFG Analysis):**

```cpp
// File: tests/CFGAnalysisTest.cpp

#include "CFGAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>

void test_CFGDetectsAllReturns() {
    std::cout << "Running test_CFGDetectsAllReturns... ";

    const char *Code = R"(
        void func(int flag) {
            int x = 10;
            if (flag) return;  // Early return
            int y = 20;
            return;  // Normal return
        }
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Find function
    clang::FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<clang::FunctionDecl>(D)) {
            if (Func->getNameAsString() == "func") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'func' not found");

    // Build CFG and analyze
    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: 2 exit points (2 return statements)
    assert(analyzer.getExitPointCount() == 2);

    std::cout << "✓" << std::endl;
}

int main() {
    test_CFGDetectsAllReturns();
    return 0;
}
```

### Step 2: GREEN - Implement Minimal Code

**Example for Story #151:**

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

    void analyzeCFG(FunctionDecl *FD);

    int getExitPointCount() const { return exitPoints.size(); }
    int getLocalVarCount() const { return localVars.size(); }
    int getScopeCount() const { return scopes.size(); }

private:
    std::unique_ptr<CFG> cfg;
    std::vector<CFGBlock*> exitPoints;
    std::vector<VarDecl*> localVars;
    std::vector<CompoundStmt*> scopes;

    void findExitPoints();
    void findLocalVars(FunctionDecl *FD);
    void findScopes(FunctionDecl *FD);
};

} // namespace clang

#endif
```

```cpp
// File: src/CFGAnalyzer.cpp

#include "CFGAnalyzer.h"
#include "clang/AST/RecursiveASTVisitor.h"

using namespace clang;

void CFGAnalyzer::analyzeCFG(FunctionDecl *FD) {
    // Build CFG
    CFG::BuildOptions options;
    options.AddImplicitDtors = true;

    cfg = CFG::buildCFG(FD, FD->getBody(), &FD->getASTContext(), options);

    if (!cfg) return;

    findExitPoints();
    findLocalVars(FD);
    findScopes(FD);
}

void CFGAnalyzer::findExitPoints() {
    for (auto *Block : *cfg) {
        if (Block->getTerminator().isValid()) {
            if (llvm::isa<ReturnStmt>(Block->getTerminatorStmt())) {
                exitPoints.push_back(Block);
            }
        }
    }
}

void CFGAnalyzer::findLocalVars(FunctionDecl *FD) {
    class VarFinder : public RecursiveASTVisitor<VarFinder> {
    public:
        std::vector<VarDecl*> &vars;
        VarFinder(std::vector<VarDecl*> &v) : vars(v) {}

        bool VisitVarDecl(VarDecl *VD) {
            if (VD->isLocalVarDecl())
                vars.push_back(VD);
            return true;
        }
    };

    VarFinder finder(localVars);
    finder.TraverseStmt(FD->getBody());
}

void CFGAnalyzer::findScopes(FunctionDecl *FD) {
    class ScopeFinder : public RecursiveASTVisitor<ScopeFinder> {
    public:
        std::vector<CompoundStmt*> &scopes;
        ScopeFinder(std::vector<CompoundStmt*> &s) : scopes(s) {}

        bool VisitCompoundStmt(CompoundStmt *CS) {
            scopes.push_back(CS);
            return true;
        }
    };

    ScopeFinder finder(scopes);
    finder.TraverseStmt(FD->getBody());
}
```

### Step 3: REFACTOR - Apply SOLID/KISS/DRY

**SOLID Checklist:**
- **S**ingle Responsibility: Each class/method does ONE thing
- **O**pen/Closed: Extend behavior via inheritance, not modification
- **L**iskov Substitution: Derived classes work wherever base expected
- **I**nterface Segregation: Small, focused interfaces
- **D**ependency Inversion: Depend on abstractions, not concretions

**KISS/DRY/YAGNI:**
- Keep it simple, remove unnecessary complexity
- Don't repeat yourself - extract common code
- Don't implement features not needed yet

### Step 4: VERIFY - All Tests Pass

```bash
# Run ALL tests (not just new one)
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

# All should pass - NO REGRESSIONS ALLOWED
```

### Step 5: COMMIT & UPDATE GITHUB

```bash
# Conventional commit
git add .
git commit -m "feat(epic5): implement Story #151 - CFG Analysis Infrastructure

- Build CFG using clang::CFG::buildCFG()
- Detect all exit points (return statements)
- Track local variable declarations
- Identify nested scopes (CompoundStmt)
- Add CFGAnalyzer class with query interface
- Unit tests verify CFG construction for complex functions

Refs #151"

# Push to develop
git push origin develop
```

**Update GitHub Project Status:**

```bash
# Variables
STORY_NUM=151
PROJECT_ID="PVT_kwHOBJ7Qkc4BKHLI"
STATUS_FIELD_ID="PVTSSF_lAHOBJ7Qkc4BKHLIzg6E1IE"
DONE_OPTION_ID="98236657"

# Get item ID
ITEM_ID=$(gh project item-list 14 --owner o2alexanderfedin --format json --limit 100 | \
  jq -r ".items[] | select(.content.number == $STORY_NUM) | .id")

# Update to Done
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

---

## Testing Strategy

### Unit Tests (Per Story)

| Story | Test File | Key Tests |
|-------|-----------|-----------|
| #151 | `CFGAnalysisTest.cpp` | CFG construction, exit point detection |
| #152 | `FunctionExitDestructorTest.cpp` | Destructor injection at function end |
| #153 | `EarlyReturnDestructorTest.cpp` | Destructors before early returns |
| #154 | `NestedScopeDestructorTest.cpp` | Nested scope cleanup |
| #155 | `GotoDestructorTest.cpp` | Goto with object cleanup |
| #156 | `LoopDestructorTest.cpp` | Break/continue with destructors |
| #157 | `RAIIIntegrationTest.cpp` | End-to-end RAII scenarios |

### Integration Tests (Story #157)

1. **File RAII pattern:** Open/close with early error returns
2. **Buffer allocation:** Malloc/free with exception-like control flow
3. **Lock guard pattern:** Acquire/release in complex scope
4. **Multiple resources:** Complex cleanup ordering across scopes
5. **Nested loops:** Break/continue with objects

---

## Validation Checklist

Before marking story as "Done":

- [ ] Test file created in `tests/`
- [ ] Test initially FAILED (RED phase complete)
- [ ] Implementation added to `src/` or `include/`
- [ ] Test now PASSES (GREEN phase complete)
- [ ] Code refactored (REFACTOR phase complete)
- [ ] ALL existing tests still pass (no regressions)
- [ ] Conventional commit message created
- [ ] Code pushed to develop branch
- [ ] GitHub Project status updated to "Done"
- [ ] Code follows existing patterns from Epic #4

---

## SOLID Principles Application

### Story #151 (CFG Analysis)

**Single Responsibility:**
- `CFGAnalyzer` only analyzes CFG
- Separate methods for exit points, vars, scopes

**Open/Closed:**
- Can extend with new analysis types without modifying existing code

**Interface Segregation:**
- Clean query interface: `getExitPointCount()`, `getLocalVarCount()`, etc.

**Dependency Inversion:**
- Depends on Clang CFG API abstraction, not internal implementation

### Story #152-157 (Destructor Injection)

**Single Responsibility:**
- Each story handles ONE specific control flow case
- Separate concerns: detection vs injection

**DRY (Don't Repeat Yourself):**
- Extract common destructor injection logic
- Reuse CFG analysis from Story #151

**KISS (Keep It Simple):**
- Minimal code to achieve goal
- Clear, readable implementation

**YAGNI (You Aren't Gonna Need It):**
- Only implement CFG analysis features needed for destructor injection
- Don't over-engineer

---

## TRIZ Principles When Stuck

- **Segmentation:** Break problem into smaller pieces (already done with 7 stories)
- **Asymmetry:** Try different approaches for different control flow types
- **Dynamics:** Make code adaptable to different CFG patterns
- **Preliminary Action:** Analyze CFG before injecting destructors (Story #151 first)
- **Inversion:** Instead of tracking what to destroy, track what's NOT destroyed yet

---

## Velocity Tracking

**Target Velocity:** 6-9 SP/hour (based on Epic #19 baseline: 8.89 SP/hour)

**Expected Duration:**
- 13 SP ÷ 8.89 SP/hour = **1.46 hours**

**Actual Tracking:**
- Start time: (record when Story #151 starts)
- End time: (record when Story #157 completes)
- Actual velocity: 13 SP ÷ (end - start) hours

---

## Prerequisites Verification

Before starting Story #151:

```bash
# 1. Epic #4 complete
gh issue view 4 --json state | jq -r '.state'  # Should be "CLOSED"

# 2. All Phase 1 tests passing
./build_and_test.sh  # Or run individual tests

# 3. Build system working
cmake -S . -B build && cmake --build build  # Should succeed

# 4. Current branch
git branch --show-current  # Should be 'develop'
```

---

## Story-Specific Notes

### Story #151: CFG Analysis Infrastructure

**Key Clang APIs:**
- `CFG::buildCFG()` - Build control flow graph
- `CFGBlock::getTerminator()` - Get terminator statement (return, goto, etc.)
- `CFG::begin()`, `CFG::end()` - Iterate blocks
- `RecursiveASTVisitor` - Find VarDecls and CompoundStmts

**Edge Cases:**
- Functions with no returns (implicit return)
- Functions with only goto (no return)
- Empty functions

### Story #152: Function Exit Destructors

**Implementation:**
- Track object construction order in vector
- At function exit, inject destructors in reverse order
- Handle implicit returns (no explicit return statement)

**Edge Cases:**
- Function with no local objects
- Objects with trivial destructors (skip)

### Story #153: Early Return Destructors

**Implementation:**
- For each return statement, determine which objects are in scope
- Inject destructor sequence before return
- Only destroy objects constructed up to that point

**Edge Cases:**
- Return in nested scope (destroy inner + outer)
- Multiple returns in same scope

### Story #154: Nested Scope Destruction

**Implementation:**
- Track scope depth with stack
- At closing brace, inject destructors for scope-local objects
- Maintain destruction order within scope

**Edge Cases:**
- Deeply nested scopes (5+ levels)
- Empty scopes

### Story #155: Goto Handling

**Implementation:**
- Analyze label position relative to goto
- For jump out of scope: destroy all objects between goto and label
- For jump into scope: C++ forbids (emit error or skip)

**Edge Cases:**
- Backward goto (label before goto)
- Forward goto (label after goto)
- Goto to same scope level

### Story #156: Loop Break/Continue

**Implementation:**
- Break: destroy all loop-iteration objects, then exit
- Continue: destroy iteration objects, restart loop
- Distinguish loop-scope vs iteration-scope objects

**Edge Cases:**
- Nested loops with break/continue
- Continue in do-while vs while vs for

### Story #157: Integration Testing

**Real-World Patterns:**
1. RAII file handle (inspired by `std::ifstream`)
2. RAII buffer (inspired by `std::vector`)
3. Lock guard (inspired by `std::lock_guard`)
4. Smart pointer (simple `unique_ptr`-like)
5. Scope guard (DEFER-like pattern)

---

## References

- **Epic #5 Issue:** https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/37
- **Clang CFG Docs:** https://clang.llvm.org/doxygen/classclang_1_1CFG.html
- **Clang CFG Example:** https://clang.llvm.org/doxygen/CFG_8cpp_source.html
- **ARCHITECTURE.md:** RAII section
- **PNaCl Exception Handling:** https://www.chromium.org/nativeclient/pnacl/exception-handling/

---

**Status:** Phase 2 Complete - Ready for Phase 3 Execution

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
