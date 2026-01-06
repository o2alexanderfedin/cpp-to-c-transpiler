# Implement NamespaceHandler for Dispatcher Architecture

## Objective

Create a NamespaceHandler in the dispatcher architecture (`src/dispatch/`, `include/dispatch/`) that translates C++ namespace declarations and flattens namespace-qualified names to C-compatible identifiers. This handler will follow the Chain of Responsibility pattern established by RecordHandler, FunctionHandler, and other dispatch handlers.

**Why this matters**: C doesn't have namespaces. We need to flatten namespace hierarchies (e.g., `std::vector` → `std_vector`, `MyApp::Utils::StringHelper` → `MyApp_Utils_StringHelper`) to avoid naming conflicts and maintain semantic structure. This is critical for translating C++ code that uses namespaces for organization.

## Context

### Architecture Overview

The transpiler uses a 3-stage pipeline:
1. **Stage 1**: C++ source → C++ AST (Clang frontend)
2. **Stage 2**: C++ AST → C AST (CppToCVisitor with dispatcher handlers)
3. **Stage 3**: C AST → C source files (CodeGenerator)

We're implementing Stage 2 handlers using the Chain of Responsibility pattern.

### Existing Dispatcher Architecture

**Pattern**: All handlers in `dispatch/` follow this structure:

```cpp
class SomeHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);
private:
    static bool canHandle(const clang::Decl* D);  // Predicate
    static void handleSomething(...);              // Visitor
};
```

**Integration Points**:
- `CppToCVisitorDispatcher` - central dispatcher with `dispatch(cppCtx, cCtx, node)` methods
- `NodeMapper<KeyT, ValueT>` - generic mapper for C++ node → C node mappings
- `DeclMapper` - type alias for `NodeMapper<clang::Decl, clang::Decl*>`
- `PathMapper` - maps C++ source files to C target files

### Reference Implementations

**Study these handlers**:
- `include/dispatch/RecordHandler.h` + `src/dispatch/RecordHandler.cpp` - name mangling pattern for nested structs
- `include/dispatch/FunctionHandler.h` + `src/dispatch/FunctionHandler.cpp` - declaration handler pattern
- `src/NameMangler.cpp` - existing namespace handling logic (lines 133, 168)

**Key Patterns from RecordHandler**:
1. **Name mangling**: `Outer_Inner` pattern (use same for namespaces: `Namespace_Name`)
2. **Static registration**: `registerWith(dispatcher)` registers predicate + visitor
3. **Exact type matching**: `D->getKind() == Decl::Namespace`
4. **DeclMapper storage**: Store mapping after creation

### Namespace Handling Strategy

C doesn't have namespaces, so we flatten them:

```cpp
// C++:
namespace MyApp {
    namespace Utils {
        class StringHelper {
            static void trim(std::string& s);
        };
    }
}

// C (flattened):
// No NamespaceDecl in C AST
// Names are prefixed: MyApp_Utils_StringHelper
//                     MyApp_Utils_StringHelper_trim
```

**Two responsibilities**:
1. **Process NamespaceDecl** - Track namespace hierarchy but don't emit to C AST
2. **Mangle names** - Prefix declarations inside namespaces with namespace path

## Requirements

### Phase 1 Scope: Namespace Name Flattening

Implement NamespaceHandler with these features:

1. **NamespaceDecl Processing**
   - Match `clang::NamespaceDecl`
   - Track namespace hierarchy (for name prefixing)
   - Don't create C NamespaceDecl (C has no namespaces)
   - Store mapping in DeclMapper for reference tracking

2. **Namespace Name Mangling**
   - Compute namespace path (e.g., `MyApp::Utils`)
   - Use `_` separator for flattening (e.g., `MyApp_Utils`)
   - Store namespace prefix for child declarations
   - Apply prefix when translating declarations inside namespace

3. **Nested Namespace Support**
   - Handle nested namespaces (C++17: `namespace A::B::C {}`)
   - Compute full path recursively
   - Example: `namespace A { namespace B { ... } }` → prefix `A_B_`

4. **Anonymous Namespace Handling**
   - Detect anonymous namespaces (unnamed)
   - Generate unique identifier (e.g., `__anon_123`)
   - Use same approach as NameMangler.cpp:133 `getAnonymousNamespaceID()`

5. **Child Declaration Processing**
   - Recursively dispatch child declarations (functions, classes, etc.)
   - Apply namespace prefix to child names
   - Coordinate with FunctionHandler, RecordHandler for name prefixing

### Exclusions (Future Phases)

**Do NOT implement** in this phase:
- ❌ Using directives (`using namespace std;`)
- ❌ Using declarations (`using std::vector;`)
- ❌ Namespace aliases (`namespace fs = std::filesystem;`)
- ❌ Inline namespaces
- ❌ ADL (Argument-Dependent Lookup) resolution

For unsupported features, log a warning:
```cpp
llvm::errs() << "[NamespaceHandler] Warning: Using directives not supported, skipping\n";
```

### Implementation Checklist

- [ ] Create `include/dispatch/NamespaceHandler.h`
  - [ ] Handler class with static methods: `registerWith()`, `canHandle()`, `handleNamespace()`
  - [ ] Helper methods: `getNamespacePath()`, `generateAnonymousID()`, `processChildDecls()`
  - [ ] Comprehensive documentation with translation examples

- [ ] Create `src/dispatch/NamespaceHandler.cpp`
  - [ ] `registerWith()` - register predicate + visitor with dispatcher
  - [ ] `canHandle()` - match NamespaceDecl (exact type matching with `getKind()`)
  - [ ] `handleNamespace()` - main translation logic
    - [ ] Check if already processed via `declMapper.hasCreated()`
    - [ ] Detect anonymous vs named namespaces
    - [ ] Compute namespace path (recursive for nested)
    - [ ] Store namespace mapping (for reference tracking)
    - [ ] Recursively dispatch child declarations
    - [ ] Apply namespace prefix to child names

- [ ] Update name prefixing in other handlers
  - [ ] Modify `FunctionHandler` to check for namespace parent
  - [ ] Modify `RecordHandler` to check for namespace parent
  - [ ] Apply namespace prefix when creating C declarations

- [ ] Update `CMakeLists.txt`
  - [ ] Add `src/dispatch/NamespaceHandler.cpp` to build targets

- [ ] Register handler in dispatcher initialization
  - [ ] Find where handlers are registered
  - [ ] Add `NamespaceHandler::registerWith(dispatcher)`

- [ ] Create unit tests: `tests/unit/dispatch/NamespaceHandlerDispatcherTest.cpp`
  - [ ] Test basic namespace (single level)
  - [ ] Test nested namespaces (multiple levels)
  - [ ] Test anonymous namespace
  - [ ] Test function in namespace (verify name prefixing)
  - [ ] Test class in namespace (verify name prefixing)
  - [ ] Test already-processed detection (DeclMapper)
  - [ ] Test namespace path computation

- [ ] Run all tests
  - [ ] Build: `cmake --build build`
  - [ ] Run unit tests: `ctest --test-dir build -R NamespaceHandlerDispatcherTest`
  - [ ] Fix any failures

- [ ] Integration test (optional but recommended)
  - [ ] Test full pipeline with namespaced functions
  - [ ] Verify name mangling in emitted C code

## Output Specification

### Files to Create

1. **include/dispatch/NamespaceHandler.h**
   - Location: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/dispatch/NamespaceHandler.h`
   - Pattern: Follow RecordHandler.h structure
   - Documentation: Class-level and method-level comments

2. **src/dispatch/NamespaceHandler.cpp**
   - Location: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/NamespaceHandler.cpp`
   - Pattern: Follow RecordHandler.cpp structure
   - Logging: Use `llvm::outs()` for debug messages, `llvm::errs()` for warnings

3. **tests/unit/dispatch/NamespaceHandlerDispatcherTest.cpp**
   - Location: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/unit/dispatch/NamespaceHandlerDispatcherTest.cpp`
   - Framework: Google Test (like other dispatcher tests)
   - Pattern: Follow RecordHandlerDispatcherTest.cpp structure

### Files to Modify

1. **CMakeLists.txt**
   - Add `src/dispatch/NamespaceHandler.cpp` to existing handler list
   - Add test executable target for NamespaceHandlerDispatcherTest

2. **Dispatcher registration site** (find where handlers are registered)
   - Add `#include "dispatch/NamespaceHandler.h"`
   - Add `NamespaceHandler::registerWith(dispatcher);`

3. **FunctionHandler.cpp** (optional - if integrating name prefixing)
   - Add namespace prefix check in `handleFunction()`
   - Apply prefix to function name if parent is namespace

4. **RecordHandler.cpp** (optional - if integrating name prefixing)
   - Add namespace prefix check in `handleRecord()`
   - Apply prefix to struct name if parent is namespace

### Code Structure Template

```cpp
// include/dispatch/NamespaceHandler.h
#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/Decl.h"

namespace cpptoc {

class NamespaceHandler {
public:
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    static bool canHandle(const clang::Decl* D);

    static void handleNamespace(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    // Helper: Compute namespace path (e.g., "A::B::C" → "A_B_C")
    static std::string getNamespacePath(const clang::NamespaceDecl* NS);

    // Helper: Generate unique ID for anonymous namespace
    static std::string generateAnonymousID(const clang::NamespaceDecl* NS);

    // Helper: Process child declarations with namespace prefix
    static void processChildDecls(
        const clang::NamespaceDecl* NS,
        const std::string& namespacePrefix,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
```

## Success Criteria

### Compilation
- [ ] All files compile without errors or warnings
- [ ] CMake configuration succeeds
- [ ] Build completes successfully

### Tests
- [ ] All unit tests pass (NamespaceHandlerDispatcherTest)
- [ ] No regressions in existing tests
- [ ] Test coverage includes:
  - Basic namespace processing
  - Nested namespace path computation
  - Anonymous namespace handling
  - Function in namespace (name prefixing)
  - Class in namespace (name prefixing)
  - Already-processed detection

### Integration
- [ ] Handler registered in dispatcher
- [ ] NamespaceDecl tracked (stored in DeclMapper)
- [ ] Child declarations get namespace prefix
- [ ] Namespace path computed correctly (A::B → A_B)
- [ ] Anonymous namespaces get unique IDs

### Code Quality
- [ ] Follows SOLID principles (SRP, OCP, DIP)
- [ ] Follows existing dispatcher handler patterns
- [ ] Proper error handling (assertions, null checks)
- [ ] Debug logging for development visibility
- [ ] No code duplication (DRY)
- [ ] Comments explain why, not what

## Edge Cases to Handle

1. **Global namespace declarations**:
   ```cpp
   void globalFunc();  // No namespace prefix
   ```
   - Check if `getDeclContext()` is `TranslationUnitDecl`, not `NamespaceDecl`

2. **Nested namespaces (C++17 syntax)**:
   ```cpp
   namespace A::B::C { ... }
   ```
   - Parse nested namespace chain
   - Compute full path: `A_B_C`

3. **Anonymous namespaces**:
   ```cpp
   namespace { void helperFunc(); }
   ```
   - Generate unique ID (use source location or counter)
   - Apply prefix: `__anon_<id>_helperFunc`

4. **Multiple namespace blocks**:
   ```cpp
   namespace A { void foo(); }
   namespace A { void bar(); }  // Same namespace, different block
   ```
   - Use same prefix for both blocks
   - NamespaceDecl may have multiple definitions

5. **Inline namespaces** (C++11):
   ```cpp
   inline namespace v2 { ... }
   ```
   - Log warning (not supported)
   - Skip or treat as regular namespace

## Resources

### Clang AST API References

- `clang::NamespaceDecl::Create()` - create namespace decl (NOT used in C AST)
- `NamespaceDecl::isAnonymousNamespace()` - check if unnamed
- `NamespaceDecl::decls()` - iterate over child declarations
- `DeclContext::getDeclContext()` - get parent context
- `NamedDecl::getQualifiedNameAsString()` - get fully qualified name

### Existing Code References

**Dispatcher Pattern**:
- `include/dispatch/CppToCVisitorDispatcher.h:77-253` - Dispatcher class
- `src/dispatch/RecordHandler.cpp:21-26` - Handler registration pattern
- `src/dispatch/RecordHandler.cpp:28-35` - Exact type matching with `getKind()`

**Name Mangling**:
- `src/dispatch/RecordHandler.cpp:267-269` - getMangledName() helper (uses `_` separator)
- `src/NameMangler.cpp:133` - getAnonymousNamespaceID() existing implementation

**Mapper Usage**:
- `include/mapping/NodeMapper.h` - Generic mapper template
- `src/dispatch/RecordHandler.cpp:50-55` - Check if already processed

### Documentation

Read before implementing:
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/CLAUDE.md` - Architecture principles
- `include/dispatch/RecordHandler.h` - Well-documented handler with name mangling
- `src/NameMangler.cpp` - Existing namespace handling patterns

## SUMMARY.md Requirement

After completing the implementation, you MUST create:

**File**: `.prompts/050-namespace-handler-do/SUMMARY.md`

**Required Sections**:
```markdown
# NamespaceHandler Implementation Summary

**{One substantive sentence describing what was accomplished}**

## Version
v1 - Initial implementation

## Files Created
- include/dispatch/NamespaceHandler.h
- src/dispatch/NamespaceHandler.cpp
- tests/unit/dispatch/NamespaceHandlerDispatcherTest.cpp

## Key Implementation Details
- {Bullet points of important decisions made}
- {Name mangling pattern used}
- {How namespace hierarchy is tracked}

## Test Results
- {Pass/fail status}
- {Coverage summary}

## Decisions Needed
- {Any open questions or choices user must make}
- {Or "None" if implementation is complete}

## Blockers
- {External dependencies or issues}
- {Or "None" if unblocked}

## Next Step
{Concrete next action, e.g., "Integrate with FunctionHandler for name prefixing" or "Test with real-world namespaced code"}
```

## Implementation Notes

### TDD Approach (Recommended)

1. **Red**: Write failing test first
   ```cpp
   TEST(NamespaceHandlerDispatcherTest, BasicNamespace) {
       // Create C++ namespace AST
       // Call handler
       // Assert namespace tracked, child names prefixed
       FAIL(); // Test fails initially
   }
   ```

2. **Green**: Write minimal code to pass
   ```cpp
   void NamespaceHandler::handleNamespace(...) {
       // Minimal implementation to pass test
   }
   ```

3. **Refactor**: Clean up while tests stay green
   ```cpp
   // Extract helpers, remove duplication
   // Tests still pass
   ```

### Namespace Path Computation Algorithm

```cpp
std::string NamespaceHandler::getNamespacePath(const NamespaceDecl* NS) {
    std::vector<std::string> nameParts;

    // Walk up namespace hierarchy
    const DeclContext* DC = NS;
    while (DC && isa<NamespaceDecl>(DC)) {
        const auto* nsDecl = cast<NamespaceDecl>(DC);
        if (!nsDecl->isAnonymousNamespace()) {
            nameParts.push_back(nsDecl->getNameAsString());
        }
        DC = DC->getParent();
    }

    // Reverse (we walked from inner to outer)
    std::reverse(nameParts.begin(), nameParts.end());

    // Join with '_' separator
    return llvm::join(nameParts, "_");
}
```

### Integration with Other Handlers

When other handlers create declarations, check for namespace parent:

```cpp
// In FunctionHandler::handleFunction()
std::string funcName = cppFunc->getNameAsString();

// Check if function is in namespace
if (const auto* nsDecl = dyn_cast<NamespaceDecl>(cppFunc->getDeclContext())) {
    std::string nsPrefix = NamespaceHandler::getNamespacePath(nsDecl);
    funcName = nsPrefix + "_" + funcName;
}

// Create C function with prefixed name
```

### Debugging Tips

- Use `llvm::outs()` for progress messages
- Use `llvm::errs()` for warnings/errors
- Print namespace hierarchy: `NS->printQualifiedName(llvm::outs())`
- Check parent context: `DC->getDeclKindName()`
- Verify name mangling: log original and mangled names

### Common Pitfalls

1. **Forgetting to process child declarations**: Must recursively dispatch children
2. **Not handling anonymous namespaces**: Check `isAnonymousNamespace()` first
3. **Incorrect hierarchy traversal**: Walk from inner to outer, then reverse
4. **Missing integration**: Other handlers must apply namespace prefix
5. **Creating C NamespaceDecl**: C has no namespaces - only track for prefixing
6. **Duplicate namespace processing**: Check `declMapper.hasCreated()` first

### Logging Convention

```cpp
llvm::outs() << "[NamespaceHandler] Processing namespace: " << NS->getNameAsString() << "\n";
llvm::outs() << "[NamespaceHandler] Computed path: A::B → A_B\n";
llvm::outs() << "[NamespaceHandler] Anonymous namespace detected, ID: " << anonID << "\n";
llvm::errs() << "[NamespaceHandler] Warning: Using directive not supported\n";
```

## Design Decisions to Make

### 1. Namespace Prefix Storage

**Option A**: Store prefix in DeclMapper metadata
- Store `NamespaceDecl → namespace_path` mapping
- Other handlers query DeclMapper for prefix

**Option B**: Store prefix in separate map
- Create `NamespacePrefixMapper` class
- Store `DeclContext* → std::string` mapping

**Recommendation**: Use DeclMapper with a helper function `getNamespacePrefix(DeclContext*)` that walks up the context hierarchy.

### 2. Anonymous Namespace ID Generation

**Option A**: Use source location hash
```cpp
unsigned hash = NS->getLocation().getRawEncoding();
return "__anon_" + std::to_string(hash);
```

**Option B**: Use static counter
```cpp
static unsigned counter = 0;
return "__anon_" + std::to_string(++counter);
```

**Recommendation**: Use source location (deterministic, same across runs).

### 3. Handler Registration Order

Namespace handler should run **before** FunctionHandler and RecordHandler:
- NamespaceHandler tracks hierarchy first
- FunctionHandler/RecordHandler apply prefix after

Registration order matters in dispatcher.

## Final Checklist Before Completion

- [ ] All files created in correct locations
- [ ] Handler registered with dispatcher (before FunctionHandler/RecordHandler)
- [ ] All tests pass (unit + existing tests)
- [ ] No compiler warnings
- [ ] Code follows project conventions (CLAUDE.md guidelines)
- [ ] SUMMARY.md created with substantive content
- [ ] Integration tested with functions/classes in namespaces
- [ ] Committed and pushed to git
- [ ] Ready for next phase (using directives, namespace aliases)
