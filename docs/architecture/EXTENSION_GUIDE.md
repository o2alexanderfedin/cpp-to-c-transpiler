# Extension Guide

**How to Extend the C++ to C Transpiler**

This guide shows you how to add support for new C++ features or customize the transpiler's behavior.

## Table of Contents

1. [Extension Points](#extension-points)
2. [Adding a New Feature](#adding-a-new-feature)
3. [Adding a Visitor Method](#adding-a-visitor-method)
4. [Creating a Feature Translator](#creating-a-feature-translator)
5. [Adding Runtime Support](#adding-runtime-support)
6. [Real-World Examples](#real-world-examples)

## Extension Points

The transpiler provides several extension points:

```
┌─────────────────────────────────────┐
│  CppToCVisitor (Main Entry Point)   │
├─────────────────────────────────────┤
│  + VisitNewConstruct()              │ ← Add visitor method
│  + Dispatch to translator           │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│  NewFeatureTranslator               │ ← Create translator
├─────────────────────────────────────┤
│  + translate()                      │
│  + analyze()                        │
│  + generateCode()                   │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│  CNodeBuilder                       │ ← Add helpers
├─────────────────────────────────────┤
│  + newFeatureHelper()               │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│  Runtime Library                    │ ← Add runtime
├─────────────────────────────────────┤
│  new_feature_runtime.c              │
└─────────────────────────────────────┘
```

## Adding a New Feature

Let's walk through adding support for a new C++ feature: **Range-based for loops**.

### Step 1: Analyze the Feature

**C++ Code**:
```cpp
std::vector<int> vec = {1, 2, 3};
for (int x : vec) {
    printf("%d\n", x);
}
```

**Desired C Output**:
```c
struct vector_int vec = ...;
for (int i = 0; i < vec.size; i++) {
    int x = vec.data[i];
    printf("%d\n", x);
}
```

### Step 2: Identify AST Node

Check Clang's AST:
```bash
clang -Xclang -ast-dump -fsyntax-only test.cpp
```

Output shows `CXXForRangeStmt` node:
```
CXXForRangeStmt
├─ DeclStmt (range variable: vec)
├─ DeclStmt (begin iterator)
├─ DeclStmt (end iterator)
├─ BinaryOperator (begin != end)
├─ UnaryOperator (++begin)
├─ DeclStmt (loop variable: x)
└─ CompoundStmt (body)
```

### Step 3: Add Visitor Method

**File**: `include/CppToCVisitor.h`
```cpp
class CppToCVisitor : public RecursiveASTVisitor<CppToCVisitor> {
public:
    bool VisitCXXForRangeStmt(CXXForRangeStmt *S);
};
```

**File**: `src/CppToCVisitor.cpp`
```cpp
bool CppToCVisitor::VisitCXXForRangeStmt(CXXForRangeStmt *S) {
    // Dispatch to translator
    RangeForTranslator translator(Ctx, Builder);
    Stmt *transformedStmt = translator.translate(S);

    // Replace in AST (or record for later)
    recordTranslation(S, transformedStmt);

    return true;
}
```

### Step 4: Create Feature Translator

**File**: `include/RangeForTranslator.h`
```cpp
#pragma once

#include <clang/AST/Stmt.h>
#include "CNodeBuilder.h"

namespace cpptoc {

class RangeForTranslator {
    ASTContext &Ctx;
    CNodeBuilder &Builder;

public:
    RangeForTranslator(ASTContext &Ctx, CNodeBuilder &Builder)
        : Ctx(Ctx), Builder(Builder) {}

    Stmt* translate(CXXForRangeStmt *S);

private:
    Stmt* translateVectorLoop(CXXForRangeStmt *S);
    Stmt* translateArrayLoop(CXXForRangeStmt *S);
    bool isVector(QualType T);
};

} // namespace cpptoc
```

**File**: `src/RangeForTranslator.cpp`
```cpp
#include "RangeForTranslator.h"
#include <clang/AST/Decl.h>

using namespace clang;
using namespace cpptoc;

Stmt* RangeForTranslator::translate(CXXForRangeStmt *S) {
    // Get range variable
    VarDecl *RangeVar = S->getRangeStmt()->getSingleDecl();
    QualType RangeType = RangeVar->getType();

    // Dispatch based on type
    if (isVector(RangeType)) {
        return translateVectorLoop(S);
    } else if (RangeType->isArrayType()) {
        return translateArrayLoop(S);
    }

    // Fallback: use iterators
    return translateIteratorLoop(S);
}

Stmt* RangeForTranslator::translateVectorLoop(CXXForRangeStmt *S) {
    VarDecl *RangeVar = S->getRangeStmt()->getSingleDecl();
    VarDecl *LoopVar = S->getLoopVariable();
    Stmt *Body = S->getBody();

    // Create: int i = 0;
    VarDecl *IndexVar = Builder.intVar("i", 0);
    DeclStmt *InitStmt = Builder.declStmt(IndexVar);

    // Create: i < vec.size
    Expr *VecRef = Builder.ref(RangeVar);
    Expr *SizeAccess = Builder.member(VecRef, "size");
    Expr *IndexRef = Builder.ref(IndexVar);
    Expr *Condition = Builder.lessThan(IndexRef, SizeAccess);

    // Create: i++
    Expr *Increment = Builder.unaryIncrement(IndexRef);

    // Create: int x = vec.data[i];
    Expr *DataAccess = Builder.member(VecRef, "data");
    Expr *ElementAccess = Builder.arraySubscript(DataAccess, IndexRef);
    VarDecl *NewLoopVar = Builder.varDecl(LoopVar->getType(),
                                          LoopVar->getName(),
                                          ElementAccess);
    DeclStmt *LoopVarStmt = Builder.declStmt(NewLoopVar);

    // Create: { int x = vec.data[i]; <body> }
    Stmt *NewBody = Builder.block({LoopVarStmt, Body});

    // Create: for (int i = 0; i < vec.size; i++) { ... }
    ForStmt *ForLoop = Builder.forStmt(InitStmt, Condition,
                                       Increment, NewBody);

    return ForLoop;
}
```

### Step 5: Add CNodeBuilder Helpers

**File**: `include/CNodeBuilder.h`
```cpp
class CNodeBuilder {
public:
    // ... existing methods ...

    // New helpers for range-for translation
    BinaryOperator* lessThan(Expr *LHS, Expr *RHS);
    UnaryOperator* unaryIncrement(Expr *E);
    ArraySubscriptExpr* arraySubscript(Expr *base, Expr *index);
};
```

**File**: Implementation (inline or .cpp)
```cpp
BinaryOperator* CNodeBuilder::lessThan(Expr *LHS, Expr *RHS) {
    return new (Ctx) BinaryOperator(
        LHS, RHS, BO_LT, Ctx.BoolTy,
        VK_RValue, OK_Ordinary,
        SourceLocation(), FPOptions());
}

UnaryOperator* CNodeBuilder::unaryIncrement(Expr *E) {
    return new (Ctx) UnaryOperator(
        E, UO_PreInc, E->getType(),
        VK_LValue, OK_Ordinary,
        SourceLocation(), false);
}

ArraySubscriptExpr* CNodeBuilder::arraySubscript(Expr *base, Expr *index) {
    QualType elementType = base->getType()->getPointeeType();
    return new (Ctx) ArraySubscriptExpr(
        base, index, elementType,
        VK_LValue, OK_Ordinary,
        SourceLocation());
}
```

### Step 6: Add Tests

**File**: `tests/range_for_test.cpp`
```cpp
#include "RangeForTranslator.h"
#include <gtest/gtest.h>

TEST(RangeForTest, TranslateVectorLoop) {
    std::string input = R"(
        std::vector<int> vec = {1, 2, 3};
        for (int x : vec) {
            printf("%d", x);
        }
    )";

    std::string output = transpile(input);

    // Verify traditional for loop generated
    EXPECT_THAT(output, HasSubstr("for (int i = 0;"));
    EXPECT_THAT(output, HasSubstr("i < vec.size"));
    EXPECT_THAT(output, HasSubstr("i++)"));

    // Verify element access
    EXPECT_THAT(output, HasSubstr("vec.data[i]"));

    // Verify it compiles and runs
    ASSERT_TRUE(compileAndRun(output));
}
```

## Adding a Visitor Method

Pattern for adding new AST node handlers:

```cpp
// 1. Declare in CppToCVisitor.h
class CppToCVisitor : public RecursiveASTVisitor<CppToCVisitor> {
public:
    bool VisitNewASTNode(NewASTNode *Node);
};

// 2. Implement in CppToCVisitor.cpp
bool CppToCVisitor::VisitNewASTNode(NewASTNode *Node) {
    // Option A: Translate directly
    Stmt *translated = translateDirectly(Node);

    // Option B: Dispatch to translator
    NewFeatureTranslator translator(Ctx, Builder);
    Stmt *translated = translator.translate(Node);

    // Record translation
    recordTranslation(Node, translated);

    return true;  // Continue visiting children
}
```

## Creating a Feature Translator

Template for feature translators:

```cpp
// Header: NewFeatureTranslator.h
#pragma once

#include <clang/AST/AST.h>
#include "CNodeBuilder.h"

namespace cpptoc {

class NewFeatureTranslator {
    ASTContext &Ctx;
    CNodeBuilder &Builder;

public:
    NewFeatureTranslator(ASTContext &Ctx, CNodeBuilder &Builder);

    // Main translation entry point
    Decl* translate(CXXNewFeatureDecl *D);

private:
    // Analysis helpers
    void analyzeFeature(CXXNewFeatureDecl *D);
    bool needsSpecialHandling(CXXNewFeatureDecl *D);

    // Generation helpers
    RecordDecl* generateStruct(CXXNewFeatureDecl *D);
    FunctionDecl* generateFunction(CXXNewFeatureDecl *D);
    Stmt* generateBody(CXXNewFeatureDecl *D);
};

} // namespace cpptoc

// Implementation: NewFeatureTranslator.cpp
#include "NewFeatureTranslator.h"

using namespace clang;
using namespace cpptoc;

NewFeatureTranslator::NewFeatureTranslator(ASTContext &Ctx,
                                           CNodeBuilder &Builder)
    : Ctx(Ctx), Builder(Builder) {}

Decl* NewFeatureTranslator::translate(CXXNewFeatureDecl *D) {
    // 1. Analyze input
    analyzeFeature(D);

    // 2. Generate C structures
    RecordDecl *Struct = generateStruct(D);

    // 3. Generate C functions
    FunctionDecl *Func = generateFunction(D);

    // 4. Return translated declaration
    return Func;
}
```

## Adding Runtime Support

For features requiring runtime support:

### Step 1: Define Runtime API

**File**: `runtime/new_feature_runtime.h`
```c
#ifndef NEW_FEATURE_RUNTIME_H
#define NEW_FEATURE_RUNTIME_H

#include <stddef.h>

// Runtime support for new feature
void cxx_new_feature_init(void* data);
void cxx_new_feature_cleanup(void* data);
int cxx_new_feature_operate(void* data, int param);

#endif // NEW_FEATURE_RUNTIME_H
```

### Step 2: Implement Runtime

**File**: `runtime/new_feature_runtime.c`
```c
#include "new_feature_runtime.h"
#include <stdlib.h>

void cxx_new_feature_init(void* data) {
    // Initialize feature state
}

void cxx_new_feature_cleanup(void* data) {
    // Clean up feature state
}

int cxx_new_feature_operate(void* data, int param) {
    // Perform feature operation
    return 0;
}
```

### Step 3: Generate Calls

**File**: `src/NewFeatureTranslator.cpp`
```cpp
Stmt* NewFeatureTranslator::generateOperationCall(Expr *Object,
                                                   Expr *Param) {
    // Generate: cxx_new_feature_operate(&obj, param)
    CallExpr *Call = Builder.call("cxx_new_feature_operate", {
        Builder.addrOf(Object),
        Param
    });

    return Call;
}
```

### Step 4: Link Runtime

**File**: `runtime/CMakeLists.txt`
```cmake
add_library(cpptoc_runtime STATIC
    exception_runtime.c
    rtti_runtime.c
    new_feature_runtime.c  # Add new runtime
)
```

## Real-World Examples

### Example 1: Lambda Expressions

**Goal**: Translate lambdas to closure structs + function pointers.

**Visitor Method**:
```cpp
bool CppToCVisitor::VisitLambdaExpr(LambdaExpr *E) {
    LambdaTranslator translator(Ctx, Builder);
    Expr *translated = translator.translate(E);
    recordTranslation(E, translated);
    return true;
}
```

**Translator**:
```cpp
Expr* LambdaTranslator::translate(LambdaExpr *E) {
    // 1. Generate closure struct
    RecordDecl *Closure = generateClosureStruct(E);

    // 2. Generate function
    FunctionDecl *Func = generateLambdaFunction(E);

    // 3. Generate initializer
    Expr *Init = generateClosureInit(E, Closure, Func);

    return Init;
}
```

### Example 2: Smart Pointers

**Goal**: Translate shared_ptr to ref-counted struct.

**Generated C**:
```c
struct shared_ptr_int {
    int* ptr;
    int* ref_count;
};

void shared_ptr_int_ctor(struct shared_ptr_int* this, int* ptr) {
    this->ptr = ptr;
    this->ref_count = (int*)malloc(sizeof(int));
    *this->ref_count = 1;
}

void shared_ptr_int_copy(struct shared_ptr_int* this,
                         const struct shared_ptr_int* other) {
    this->ptr = other->ptr;
    this->ref_count = other->ref_count;
    (*this->ref_count)++;
}

void shared_ptr_int_dtor(struct shared_ptr_int* this) {
    if (--(*this->ref_count) == 0) {
        free(this->ptr);
        free(this->ref_count);
    }
}
```

### Example 3: Concepts (C++20)

**Goal**: Translate concepts to compile-time checks (if possible) or runtime asserts.

**Translation Strategy**:
- Concept constraints → static_assert in C++ phase
- Or: Generate runtime type checks
- Or: Remove entirely (duck typing in C)

## Testing Your Extension

### Unit Tests

```cpp
TEST(NewFeatureTest, BasicTranslation) {
    NewFeatureTranslator translator(Ctx, Builder);
    Decl *result = translator.translate(inputDecl);

    ASSERT_NE(result, nullptr);
    EXPECT_TRUE(isValidCDecl(result));
}
```

### Integration Tests

```cpp
TEST(IntegrationTest, NewFeatureEndToEnd) {
    std::string input = "/* C++ with new feature */";
    std::string output = transpile(input);

    EXPECT_TRUE(compileC(output));
    EXPECT_EQ(runC(output), expectedResult);
}
```

### Verification Tests

```bash
# Frama-C verification
frama-c -wp generated.c new_feature_runtime.c

# Should prove all safety properties
```

## Best Practices

1. **Start Simple**: Handle basic cases first, add complexity gradually
2. **Test Early**: Write tests before full implementation
3. **Reuse Components**: Use existing translators as patterns
4. **Document Decisions**: Explain why, not what
5. **Performance**: Measure, don't guess
6. **Frama-C**: Design for verifiability from start

## Common Pitfalls

1. **SourceLocation**: Don't forget to set source locations
2. **Memory**: Use Clang's memory management (ASTContext allocation)
3. **Types**: Always use QualType, not raw types
4. **Traversal**: Return true to continue visiting children
5. **AST Mutation**: Don't mutate C++ AST, build new C AST

## Further Reading

- [OVERVIEW.md](OVERVIEW.md) - Architecture overview
- [MODULES.md](MODULES.md) - Module documentation
- [CONTRIBUTING.md](CONTRIBUTING.md) - Contribution guidelines
- [Clang LibTooling Tutorial](https://clang.llvm.org/docs/LibTooling.html)

---

**Document Version**: 1.0
**Last Updated**: 2025-12-18
