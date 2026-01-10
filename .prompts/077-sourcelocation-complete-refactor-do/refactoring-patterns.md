# SourceLocation Refactoring Patterns

## Core Patterns

### Pattern 1: Declaration Handler (Has Decl* Parameter)

**When to use**: Handler function has access to a `const clang::Decl* D` parameter

```cpp
// Add includes at top of file
#include "SourceLocationMapper.h"
#include "TargetContext.h"

// In handler function:
std::string targetPath = disp.getCurrentTargetPath();
if (targetPath.empty()) {
    targetPath = disp.getTargetPath(cppASTContext, D);
}
SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

// Use targetLoc for all AST node creation:
clang::SomeDecl* someDecl = clang::SomeDecl::Create(
    cASTContext,
    parent,
    targetLoc,  // Was: clang::SourceLocation()
    targetLoc,  // Was: clang::SourceLocation()
    ...
);
```

**Handlers using this pattern**:
- ConstructorHandler
- VariableHandler
- VirtualMethodHandler
- InstanceMethodHandler
- MethodHandler
- RecordHandler
- EnumTranslator
- ParameterHandler

### Pattern 2: Expression/Statement Handler (No Decl Available)

**When to use**: Handler works with expressions or statements (no Decl* parameter available)

```cpp
// Add includes at top of file
#include "SourceLocationMapper.h"
#include "TargetContext.h"
#include <cassert>

// In handler function:
std::string targetPath = disp.getCurrentTargetPath();
assert(!targetPath.empty() && "Target path must be set before expression handling");
SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

// Use targetLoc for all AST node creation:
clang::SomeExpr* someExpr = clang::SomeExpr::Create(
    cASTContext,
    arg1,
    arg2,
    targetLoc,  // Was: clang::SourceLocation()
    ...
);
```

**Why assertion instead of fallback**:
- `getTargetPath()` requires a valid `const clang::Decl*` parameter
- Expression/statement handlers don't have Decl available
- Passing `nullptr` causes segfault
- Assertion enforces design invariant: `setCurrentTargetPath()` must be called before expression/statement handling

**Handlers using this pattern**:
- All expression handlers (25 handlers)
- All statement handlers (11 handlers)

## Special Cases

### Case 1: Multiple Locations in Single AST Node

**Problem**: Some AST nodes take multiple SourceLocation parameters (start, name, end, etc.)

**Solution**: Reuse same `targetLoc` for all locations

```cpp
clang::FunctionDecl* func = clang::FunctionDecl::Create(
    cASTContext,
    parent,
    targetLoc,  // StartLoc
    targetLoc,  // NameLoc (reuse same location)
    name,
    funcType,
    ...
);
```

**Example from ConstructorHandler**:
```cpp
clang::FunctionDecl* cFunc = clang::FunctionDecl::Create(
    cASTContext,
    cRecordDecl,
    targetLoc,  // Line 192
    targetLoc,  // Line 193
    &II,
    funcType,
    ...
);
```

### Case 2: DeclarationNameInfo

**Problem**: DeclarationNameInfo requires location parameter

**Before**:
```cpp
clang::DeclarationNameInfo(name, clang::SourceLocation())
```

**After**:
```cpp
clang::DeclarationNameInfo(name, targetLoc)
```

**Example from MemberExprHandler (line 105)**:
```cpp
clang::MemberExpr* cMemberExpr = clang::MemberExpr::Create(
    cASTContext,
    cBase,
    isArrow,
    targetLoc,
    clang::NestedNameSpecifierLoc(),
    targetLoc,
    cMemberDecl,
    clang::DeclAccessPair::make(cMemberDecl, clang::AS_public),
    clang::DeclarationNameInfo(cMemberDecl->getDeclName(), targetLoc),  // ← HERE
    nullptr,
    cppMemberExpr->getType(),
    cppMemberExpr->getValueKind(),
    cppMemberExpr->getObjectKind(),
    clang::NOUR_None
);
```

### Case 3: Conditional Location

**Problem**: Ternary expression with SourceLocation() as fallback

**Before**:
```cpp
cppElse ? IS->getElseLoc() : clang::SourceLocation()
```

**After**:
```cpp
cppElse ? IS->getElseLoc() : targetLoc
```

**Example from StatementHandler (line 215)**:
```cpp
clang::IfStmt* cIf = clang::IfStmt::Create(
    cASTContext,
    targetLoc,
    clang::IfStatementKind::Ordinary,
    nullptr,
    cppCondDecl,
    cCond,
    targetLoc,
    targetLoc,
    cThen,
    cppElse ? IS->getElseLoc() : targetLoc,  // ← Conditional location
    cElse
);
```

### Case 4: TypeSourceInfo with Location

**Problem**: Some `getTrivialTypeSourceInfo()` calls require location parameter

**Before**:
```cpp
cASTContext.getTrivialTypeSourceInfo(type)
```

**After** (if location overload exists):
```cpp
cASTContext.getTrivialTypeSourceInfo(type, targetLoc)
```

**Note**: Not all AST nodes require this - check API documentation

### Case 5: Function Signature Updates

**Problem**: Helper functions that create AST nodes need targetLoc parameter

**Solution**: Add `clang::SourceLocation targetLoc` parameter to helper function

**Example from MethodHandler** (createThisParameter):

**Before**:
```cpp
clang::ParmVarDecl* MethodHandler::createThisParameter(
    clang::ASTContext& cASTContext,
    clang::FunctionDecl* cFunc,
    clang::RecordDecl* cRecordDecl
) {
    // ...
    clang::RecordDecl* cThisStruct = clang::RecordDecl::Create(
        cASTContext,
        clang::TTK_Struct,
        cFunc->getDeclContext(),
        clang::SourceLocation(),  // ← Invalid
        clang::SourceLocation(),  // ← Invalid
        &II
    );
}
```

**After**:
```cpp
clang::ParmVarDecl* MethodHandler::createThisParameter(
    clang::ASTContext& cASTContext,
    clang::FunctionDecl* cFunc,
    clang::RecordDecl* cRecordDecl,
    clang::SourceLocation targetLoc  // ← NEW PARAMETER
) {
    // ...
    clang::RecordDecl* cThisStruct = clang::RecordDecl::Create(
        cASTContext,
        clang::TTK_Struct,
        cFunc->getDeclContext(),
        targetLoc,  // ← Valid
        targetLoc,  // ← Valid
        &II
    );
}
```

**Then update all callers to pass targetLoc**

### Case 6: Reusing targetLoc in Same Function

**Efficiency**: Calculate targetLoc once per function, reuse for all AST nodes

```cpp
void SomeHandler::handleSomething(...) {
    // Calculate once at start
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, D);
    }
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Reuse for all AST nodes in this function
    clang::Decl* decl1 = createDecl1(..., targetLoc);
    clang::Decl* decl2 = createDecl2(..., targetLoc);
    clang::Expr* expr1 = createExpr1(..., targetLoc);
    // ... etc
}
```

## Edge Cases Encountered

### Edge Case 1: Passing Wrong Type to getTargetPath()

**Problem**: `getTargetPath()` signature is:
```cpp
std::string getTargetPath(const clang::ASTContext& cppASTContext, const clang::Decl* D) const;
```

**Error**: Passing `Stmt*` or `Expr*` instead of `Decl*` causes type error or segfault

**Solution**: Expression/statement handlers must use Pattern 2 (assertion-based)

**Affected Handlers**:
- WhileStmtHandler
- ForStmtHandler
- IfStmtHandler
- CXXThisExprHandler
- CXXOperatorCallExprHandler

### Edge Case 2: nullptr Passed to getTargetPath()

**Problem**: `getTargetPath(cppASTContext, nullptr)` dereferences null pointer → segfault

**Symptoms**:
```
[CXXOperatorCallExprHandler] WARNING: Argument 0 not handled by any expression handler
[CXXOperatorCallExprHandler] WARNING: Argument 1 not handled by any expression handler
Segmentation fault: 11
```

**Solution**: Replace with assertion pattern (Pattern 2)

**Affected Handlers**:
- CXXOperatorCallExprHandler
- MemberExprHandler

### Edge Case 3: Helper Functions Need Dispatcher Access

**Problem**: Helper function needs to call `disp.getTargetPath()` but doesn't have dispatcher parameter

**Solution**: Add `const CppToCVisitorDispatcher& disp` parameter to helper function

**Example from DestructorHandler** (createThisParameter):

**Before**:
```cpp
static clang::ParmVarDecl* createThisParameter(
    clang::ASTContext& cASTContext,
    clang::FunctionDecl* cFunc,
    clang::RecordDecl* cRecordDecl
);
```

**After**:
```cpp
static clang::ParmVarDecl* createThisParameter(
    const CppToCVisitorDispatcher& disp,  // ← NEW
    const clang::ASTContext& cppASTContext,  // ← NEW (for getTargetPath)
    clang::ASTContext& cASTContext,
    clang::FunctionDecl* cFunc,
    clang::RecordDecl* cRecordDecl
);
```

## Verification Checklist

After refactoring a handler, verify:

- [ ] ✅ Includes added (`SourceLocationMapper.h`, `TargetContext.h`, `<cassert>` if needed)
- [ ] ✅ targetLoc calculated at start of function using correct pattern
- [ ] ✅ **ALL** `clang::SourceLocation()` replaced with `targetLoc`
- [ ] ✅ Conditional locations updated (ternary expressions)
- [ ] ✅ DeclarationNameInfo locations updated
- [ ] ✅ Helper function signatures updated if needed
- [ ] ✅ Helper function callers updated to pass targetLoc
- [ ] ✅ File compiles without errors
- [ ] ✅ Grep confirms ZERO `clang::SourceLocation()` in file
- [ ] ✅ Handler unit tests pass

## Testing Strategy

1. **Per-Handler Testing**: Run handler-specific unit tests after each refactoring
2. **Incremental Building**: Build after each wave to catch compilation errors early
3. **Segfault Detection**: Watch for segfault patterns indicating nullptr issues
4. **Final Grep**: Confirm ZERO `clang::SourceLocation()` across all dispatch/ files
5. **Full Test Suite**: Run complete test suite to ensure no regressions

## Common Mistakes to Avoid

1. ❌ **Don't** pass `nullptr` to `getTargetPath(cppASTContext, nullptr)` - causes segfault
2. ❌ **Don't** pass `Stmt*` or `Expr*` to `getTargetPath()` - expects `Decl*`
3. ❌ **Don't** forget to update helper function signatures when they create AST nodes
4. ❌ **Don't** forget to update all callers when adding targetLoc parameter
5. ❌ **Don't** use Pattern 1 for expression/statement handlers - use Pattern 2
6. ❌ **Don't** forget `#include <cassert>` when using Pattern 2
7. ❌ **Don't** leave any `clang::SourceLocation()` calls behind - verify with grep

## Benefits of Valid SourceLocations

1. **CodeGenerator Integration**: Enables `printDeclWithLineDirective()` to emit #line directives
2. **Debugging**: C code points back to correct output file locations
3. **Source Mapping**: Maintains traceability from C++ source → C output
4. **AST Consistency**: All C AST nodes have valid, non-invalid locations
5. **Future-Proofing**: Enables advanced debugging features and source mapping tools
