# Phase 53 Plan: Using Declarations and Type Aliases

**Phase**: 53
**Roadmap**: `../../ROADMAP.md`
**Brief**: `../../BRIEF.md`
**Target Version**: v2.13.0
**Status**: COMPLETE
**Priority**: MEDIUM
**Prerequisite**: Phase 48 (Namespaces)

## Phase Goal

Implement support for C++ `using` declarations, focusing on type aliases (`using MyType = ...`) which provide the highest value for transpilation. Generate equivalent C `typedef` declarations while maintaining type equivalence and integration with existing namespace and template systems.

## Business Value

Type aliases are fundamental to modern C++ and required for:
- Type simplification and abstraction
- Template type aliases (future work)
- Compatibility with standard library patterns
- Code readability and maintainability

**Impact**: Enables transpilation of C++ code using modern type alias syntax, expanding the range of supported C++ codebases.

## Deliverables

### Source Code
- [x] `include/handlers/TypeAliasAnalyzer.h` - Type alias analysis interface
- [x] `src/handlers/TypeAliasAnalyzer.cpp` - Implementation
- [x] `include/handlers/TypedefGenerator.h` - C typedef generation interface
- [x] `src/handlers/TypedefGenerator.cpp` - Implementation
- [x] Enhanced `CppToCVisitor::VisitTypeAliasDecl` for type alias handling

### Tests
- [x] `tests/unit/handlers/TypeAliasAnalyzerTest.cpp` (16 tests)
- [x] `tests/unit/handlers/TypedefGeneratorTest.cpp` (14 tests)
- [x] `tests/e2e/phase53/simple_type_alias.cpp` (E2E validation)
- Total: 30+ tests

### Documentation
- [x] Update `.planning/phases/53-using-declarations/PHASE53-SUMMARY.md`
- [x] This PLAN.md file
- [x] Inline code documentation

### Release
- [x] Git-flow release v2.13.0
- [x] Tag and push to remote

## Technical Design

### Architecture: 3-Stage Pipeline

Following the transpiler's core architecture:

**Stage 1: C++ AST Generation (Clang Frontend)**
- Input: C++ source with `using X = Y;` declarations
- Output: TypeAliasDecl nodes in C++ AST

**Stage 2: C++ AST → C AST Translation (CppToCVisitor)**
- TypeAliasAnalyzer extracts type information from TypeAliasDecl
- TypedefGenerator creates equivalent C TypedefDecl nodes
- Output: C AST with typedef declarations

**Stage 3: C Code Emission (CodeGenerator)**
- Input: C AST with TypedefDecl nodes
- Output: `typedef UnderlyingType AliasName;` in generated C code

### TypeAliasAnalyzer Class

**Responsibilities** (Single Responsibility Principle):
- Analyze C++ type alias declarations
- Extract underlying type information
- Detect template type aliases
- Resolve chained aliases

**Interface**:
```cpp
class TypeAliasAnalyzer {
public:
  /// @brief Analyze a C++ type alias declaration
  /// @param TAD Type alias declaration from C++ AST
  /// @param Context Clang AST context
  /// @return TypeAliasInfo structure with analysis results
  TypeAliasInfo analyzeTypeAlias(const clang::TypeAliasDecl *TAD,
                                 clang::ASTContext &Context);

  /// @brief Extract the underlying type from a type alias
  QualType extractUnderlyingType(const clang::TypeAliasDecl *TAD);

  /// @brief Check if type alias is templated
  bool isTemplateTypeAlias(const clang::TypeAliasDecl *TAD);

  /// @brief Resolve chained type aliases (using C = B; using B = A;)
  QualType resolveAliasChain(QualType QT, clang::ASTContext &Context);

private:
  /// @brief Analyze simple types (int, float, etc.)
  bool analyzeSimpleType(QualType QT);

  /// @brief Analyze pointer and reference types
  bool analyzePointerType(QualType QT);

  /// @brief Analyze function pointer types
  bool analyzeFunctionPointerType(QualType QT);
};

struct TypeAliasInfo {
  std::string aliasName;
  QualType underlyingType;
  bool isTemplated;
  bool isPointer;
  bool isFunctionPointer;
  bool isConst;
  bool isVolatile;
};
```

### TypedefGenerator Class

**Responsibilities** (Single Responsibility Principle):
- Generate C typedef declarations from type alias information
- Create TypedefDecl AST nodes (not string output!)
- Handle complex types (function pointers, arrays)
- Integrate with C TranslationUnit

**Interface**:
```cpp
class TypedefGenerator {
public:
  /// @brief Generate C typedef from type alias analysis
  /// @param Info Type alias information from analyzer
  /// @param C_TU Target C translation unit
  /// @param Context Clang AST context
  /// @return Generated TypedefDecl node
  clang::TypedefDecl* generateTypedef(
      const TypeAliasInfo &Info,
      clang::TranslationUnitDecl *C_TU,
      clang::ASTContext &Context);

  /// @brief Generate typedef directly from name and type
  clang::TypedefDecl* generateTypedef(
      const std::string &name,
      QualType type,
      clang::TranslationUnitDecl *C_TU,
      clang::ASTContext &Context);

private:
  /// @brief Handle complex types (function pointers, arrays)
  clang::TypedefDecl* handleComplexType(
      const TypeAliasInfo &Info,
      clang::TranslationUnitDecl *C_TU,
      clang::ASTContext &Context);

  /// @brief Generate function pointer typedef
  clang::TypedefDecl* generateFunctionPointerTypedef(
      const std::string &name,
      const clang::FunctionProtoType *FPT,
      clang::TranslationUnitDecl *C_TU,
      clang::ASTContext &Context);
};
```

### C++ → C Translation Mapping

#### 1. Simple Type Alias

**C++**:
```cpp
using IntType = int;
IntType x = 42;
```

**C** (Generated):
```c
typedef int IntType;
int x = 42;
```

#### 2. Pointer Type Alias

**C++**:
```cpp
using IntPtr = int*;
using ConstIntPtr = const int*;
IntPtr p = nullptr;
```

**C** (Generated):
```c
typedef int* IntPtr;
typedef const int* ConstIntPtr;
int* p = NULL;
```

#### 3. Function Pointer Alias

**C++**:
```cpp
using Callback = void (*)(int, float);
using BinaryOp = int (*)(int, int);
Callback handler;
```

**C** (Generated):
```c
typedef void (*Callback)(int, float);
typedef int (*BinaryOp)(int, int);
void (*handler)(int, float);
```

#### 4. Struct/Class Type Alias

**C++**:
```cpp
struct Point { int x, y; };
using Position = Point;
Position pos;
```

**C** (Generated):
```c
struct Point { int x; int y; };
typedef struct Point Position;
struct Point pos;
```

#### 5. Chained Type Aliases

**C++**:
```cpp
using A = int;
using B = A;
using C = B;
C value = 10;
```

**C** (Generated):
```c
typedef int A;
typedef int B;  // Resolved through chain to int
typedef int C;  // Resolved through chain to int
int value = 10;
```

#### 6. Const/Volatile Qualified Aliases

**C++**:
```cpp
using ConstInt = const int;
using VolatileFloat = volatile float;
ConstInt x = 5;
```

**C** (Generated):
```c
typedef const int ConstInt;
typedef volatile float VolatileFloat;
const int x = 5;
```

### Key Features

1. **Type Alias Detection**
   - Identify TypeAliasDecl in C++ AST
   - Extract alias name and underlying type
   - Detect template type alias patterns (skip for now)
   - Handle file origin filtering (skip system headers)

2. **Underlying Type Resolution**
   - Resolve simple types (int, float, char, etc.)
   - Resolve pointer types (T*, const T*, T* const)
   - Resolve reference types (converted to pointers in C)
   - Resolve function pointer types
   - Follow alias chains to canonical type

3. **C Typedef Generation**
   - Create TypedefDecl AST nodes (Stage 2: C AST)
   - NOT string generation (that's Stage 3)
   - Integrate with C TranslationUnit
   - Preserve const/volatile qualifiers

4. **Integration Points**
   - CppToCVisitor: Add VisitTypeAliasDecl method
   - FileOriginTracker: Skip system headers
   - Template handling: Skip template patterns (handle instantiations only)

### Implementation Steps (TDD Approach)

#### Step 1: TypeAliasAnalyzer Foundation (TDD)
1. Create `TypeAliasAnalyzerTest.cpp` with failing tests
2. Implement `TypeAliasAnalyzer.h` interface
3. Implement `TypeAliasAnalyzer.cpp` to pass tests
4. Refactor and add next test batch
5. Repeat until all 16 tests pass

**Tests** (16 total):
- Simple type alias (int, float, char)
- Pointer type alias (int*, const int*)
- Const type alias (const int)
- Volatile type alias (volatile float)
- Struct type alias
- Function pointer type alias
- Chained alias (2 levels)
- Chained alias (3 levels)
- Template type alias detection (skip handling)
- Namespace-qualified type alias
- Reference type alias (int&)
- Array type alias (int[10])
- Multi-level pointer (int**)
- Const pointer vs pointer to const
- Null/edge cases
- Invalid type alias (error detection)

#### Step 2: TypedefGenerator Foundation (TDD)
1. Create `TypedefGeneratorTest.cpp` with failing tests
2. Implement `TypedefGenerator.h` interface
3. Implement `TypedefGenerator.cpp` to pass tests
4. Refactor and add next test batch
5. Repeat until all 14 tests pass

**Tests** (14 total):
- Generate simple typedef (int)
- Generate pointer typedef (int*)
- Generate const typedef (const int)
- Generate volatile typedef (volatile float)
- Generate struct typedef
- Generate function pointer typedef
- Generate typedef from TypeAliasInfo
- Multiple typedefs in same TU
- Function pointer with multiple parameters
- Function pointer with return type
- Typedef with namespace-qualified type
- Complex nested type
- Null/edge cases
- Verify TypedefDecl properties

#### Step 3: CppToCVisitor Integration
1. Add TypeAliasAnalyzer and TypedefGenerator members to CppToCVisitor.h
2. Initialize in CppToCVisitor constructor
3. Implement VisitTypeAliasDecl method:
   - Check file origin (skip system headers)
   - Check if template pattern (skip, handle instantiations only)
   - Analyze with TypeAliasAnalyzer
   - Generate typedef with TypedefGenerator
   - Typedef automatically added to C_TU
4. Add debug logging (Phase 34 pattern)

#### Step 4: E2E Validation
1. Create `tests/e2e/phase53/simple_type_alias.cpp`
2. Test simple type alias (using IntType = int)
3. Test pointer type alias (using IntPtr = int*)
4. Test chained aliases
5. Verify transpilation produces correct typedefs
6. Verify generated C code compiles

## Test Plan

### Unit Tests: 30 tests total

**TypeAliasAnalyzerTest** (16 tests):
1. SimpleTypeAlias_Int
2. SimpleTypeAlias_Float
3. PointerTypeAlias
4. ConstPointerTypeAlias
5. PointerToConstTypeAlias
6. ConstTypeAlias
7. VolatileTypeAlias
8. StructTypeAlias
9. FunctionPointerTypeAlias
10. ChainedAlias_TwoLevels
11. ChainedAlias_ThreeLevels
12. TemplateTypeAlias_Detection
13. NamespaceQualifiedAlias
14. ReferenceTypeAlias
15. MultiLevelPointer
16. NullEdgeCases

**TypedefGeneratorTest** (14 tests):
1. GenerateSimpleTypedef_Int
2. GenerateSimpleTypedef_Float
3. GeneratePointerTypedef
4. GenerateConstTypedef
5. GenerateVolatileTypedef
6. GenerateStructTypedef
7. GenerateFunctionPointerTypedef
8. GenerateFromTypeAliasInfo
9. MultipleTypedefs
10. FunctionPointerWithParameters
11. ComplexNestedType
12. NamespaceQualifiedTypedef
13. VerifyTypedefDeclProperties
14. NullEdgeCases

### E2E Test: 1 test

**E2E Test File**: `tests/e2e/phase53/simple_type_alias.cpp`
- Simple type aliases (int, float)
- Pointer type aliases
- Const/volatile qualifiers
- Chained aliases
- Verify C compilation succeeds

### Test Methodology
- **TDD**: Write failing tests first, implement to pass
- **Isolation**: Each test covers one specific pattern
- **Coverage**: Aim for ≥95% code coverage
- **Validation**: Verify generated C code compiles

## Implementation Tasks

### Task 1: Analyze Current State (Checkpoint: Understanding)
**Duration**: 1-2 hours
**Actions**:
- [x] Review Clang TypeAliasDecl API
- [x] Review existing CppToCVisitor pattern (VisitEnumDecl, VisitCXXRecordDecl)
- [x] Check Phase 48 namespace integration points
- [x] Review Phase 11 template monomorphization infrastructure
- [x] Document current state and gaps

**Verification**: Gap analysis documented, approach clear

### Task 2: Implement TypeAliasAnalyzer (Checkpoint: Analyzer)
**Duration**: 3-4 hours
**Actions**:
- [x] Create TypeAliasAnalyzer.h interface
- [x] Create TypeAliasAnalyzerTest.cpp with 16 failing tests
- [x] Implement TypeAliasAnalyzer.cpp to pass tests
- [x] Handle simple types, pointers, const/volatile
- [x] Implement alias chain resolution
- [x] Add comprehensive logging

**Verification**: All 16 TypeAliasAnalyzerTest tests pass (100%)

### Task 3: Implement TypedefGenerator (Checkpoint: Generator)
**Duration**: 3-4 hours
**Actions**:
- [x] Create TypedefGenerator.h interface
- [x] Create TypedefGeneratorTest.cpp with 14 failing tests
- [x] Implement TypedefGenerator.cpp to pass tests
- [x] Generate TypedefDecl AST nodes (not strings!)
- [x] Handle function pointer typedef generation
- [x] Add comprehensive logging

**Verification**: All 14 TypedefGeneratorTest tests pass (100%)

### Task 4: Integrate with CppToCVisitor (Checkpoint: Integration)
**Duration**: 2-3 hours
**Actions**:
- [x] Add TypeAliasAnalyzer and TypedefGenerator members
- [x] Initialize in constructor
- [x] Implement VisitTypeAliasDecl method
- [x] Add file origin filtering
- [x] Add template pattern detection (skip for now)
- [x] Add debug logging (Phase 34 pattern)

**Verification**: E2E test passes, integration successful

### Task 5: Create E2E Test (Checkpoint: Validation)
**Duration**: 1-2 hours
**Actions**:
- [x] Create simple_type_alias.cpp E2E test
- [x] Test simple aliases (int, float)
- [x] Test pointer aliases
- [x] Test chained aliases
- [x] Verify C compilation

**Verification**: E2E test passes, C code compiles

### Task 6: Documentation (Checkpoint: Docs)
**Duration**: 1 hour
**Actions**:
- [x] Create PHASE53-SUMMARY.md
- [x] Update this PLAN.md
- [x] Add inline code documentation
- [x] Document known limitations

**Verification**: Documentation complete and accurate

### Task 7: Code Review & Quality (Checkpoint: Quality)
**Duration**: 1 hour
**Actions**:
- [x] Run all linters (clang-format, clang-tidy)
- [x] Fix all warnings (zero tolerance)
- [x] Review SOLID principles adherence
- [x] Check TDD was followed
- [x] Verify no regressions (existing tests still pass)

**Verification**: All linters pass, all tests pass

### Task 8: Git-Flow Release (Checkpoint: Release)
**Duration**: 30 minutes
**Actions**:
- [x] Create git-flow release branch: `release/v2.13.0`
- [x] Ensure all tests pass
- [x] Commit version bump
- [x] Merge to main and develop
- [x] Tag: `v2.13.0`
- [x] Push to GitHub

**Verification**: GitHub release created

## Verification Criteria

### Functional Correctness
- [x] All 30 unit tests passing (100%)
- [x] E2E test passing
- [x] Simple type aliases generate correct typedefs
- [x] Pointer type aliases preserve pointer syntax
- [x] Const/volatile qualifiers preserved
- [x] Chained aliases resolve to canonical type

### Code Quality
- [x] Zero linting errors (clang-tidy, cppcheck)
- [x] Strong typing enforced (no implicit casts)
- [x] SOLID principles followed
- [x] Code coverage ≥95%
- [x] TDD methodology followed

### Integration
- [x] No conflicts with Phase 48 (Namespaces)
- [x] Ready for Phase 11 integration (Templates)
- [x] Generated C code compiles without warnings
- [x] No regressions in existing tests

## Dependencies

### External Dependencies
- Clang/LLVM 17+ (already present)
- Google Test (already present)

### Internal Dependencies
- **Requires Phase 48 (Namespaces)** - for namespace-qualified type aliases
- **Synergy with Phase 11 (Templates)** - infrastructure ready for template type aliases
- No blocking dependencies

### CAN run in parallel with:
- Phase 54 (Range-For Loops)
- Phase 55 (Friend Declarations)
- Phase 56 (Virtual Inheritance)

## Risks and Mitigation

### Risk 1: Template Type Alias Complexity (Medium Impact, High Probability)
**Mitigation**:
- Skip template patterns during AST traversal (handle instantiations only)
- Infrastructure ready for future Phase 11 integration
- Document as known limitation

### Risk 2: Alias Chain Resolution Bugs (Medium Impact, Medium Probability)
**Mitigation**:
- Comprehensive tests for 2-level and 3-level chains
- Use Clang's canonical type resolution
- Conservative approach: error on circular aliases

### Risk 3: Integration with Phase 48 (Low Impact, Low Probability)
**Mitigation**:
- Leverage existing NameMangler for namespace-qualified types
- Test namespace-qualified type aliases explicitly
- Review namespace integration tests

## Success Metrics

### Quantitative
- **Tests**: 30 tests, 100% passing
- **Coverage**: ≥95% code coverage
- **Performance**: Negligible impact on transpilation time
- **C Compilation**: 100% success rate for generated typedefs

### Qualitative
- Clean integration with existing systems
- SOLID principles followed
- TDD methodology demonstrated
- Documentation complete

## Scope Decisions (YAGNI Principle)

### ✅ In Scope (Priority 1: High Value)
- Type aliases (`using X = Y`) → C typedef
- Simple types, pointers, const/volatile
- Chained alias resolution
- Function pointer aliases
- Struct/class type aliases

### ⏸️ Deferred (Priority 2: Lower Value)
- Template type aliases (infrastructure ready, needs Phase 11 integration)
- Using directives (`using namespace std`) - low ROI for transpilation
- Namespace aliases (`namespace fs = std::filesystem`) - workaround exists
- Using declarations (`using std::string`) - low ROI

**Rationale**: Type aliases provide 80% of value with 20% of effort. Using directives and namespace aliases add complexity without significant transpilation benefit.

## Known Limitations

### Current Phase
1. **Template Type Aliases**: Infrastructure ready, skipped during traversal
   - Example: `template<typename T> using Vec = std::vector<T>;`
   - Future: Integrate with Phase 11 template monomorphization

2. **Using Directives**: Not implemented (deferred)
   - Example: `using namespace std;`
   - Workaround: Use fully qualified names

3. **Namespace Aliases**: Not implemented (deferred)
   - Example: `namespace fs = std::filesystem;`
   - Workaround: Use full namespace path

### Design Decisions
- Focus on type aliases only (highest value)
- Skip template patterns, handle instantiations
- Leverage existing namespace infrastructure from Phase 48
- Ready for future Phase 11 integration

## Next Steps

### Immediate (Phase 53 Complete)
1. **Commit and push** Phase 53 implementation
2. **Create git-flow release** v2.13.0
3. **Update roadmap** to mark Phase 53 complete

### Future Enhancements (Optional)
1. **Phase 53.1**: Template type alias monomorphization (if Phase 11 needs it)
2. **Phase 53.2**: Using directives (only if strong use case emerges)
3. **Phase 54**: Range-based for loops (next phase in roadmap)

## Related Documents

- **ROADMAP.md**: Missing features analysis and prioritization
- **MISSING-FEATURES-ROADMAP.md**: Phase 53 overview (line 88+)
- **BRIEF.md**: Project brief for C++ feature work
- **Phase 48 (Namespaces)**: Integration points for namespace-qualified types
- **Phase 11 (Templates)**: Future integration for template type aliases
- **PHASE53-SUMMARY.md**: Implementation summary and completion report

## Success Definition

This phase is **COMPLETE** when:

1. **Functionality**
   - Type aliases translate to C typedefs correctly
   - Simple types, pointers, const/volatile handled
   - Chained aliases resolve to canonical type
   - Function pointer aliases work

2. **Testing**
   - 30 unit tests pass (100%)
   - E2E test passes
   - Generated C code compiles
   - No regressions in existing tests

3. **Code Quality**
   - Zero linting errors
   - SOLID principles followed
   - TDD methodology demonstrated
   - ≥95% code coverage

4. **Documentation**
   - PHASE53-SUMMARY.md complete
   - Inline documentation complete
   - Known limitations documented

5. **Release**
   - Git-flow release v2.13.0 complete
   - GitHub release tagged
   - Ready for Phase 54 (Range-For Loops)

## Rollback Strategy

If critical issues encountered:
1. Revert to previous version (git reset --hard)
2. File GitHub issue with bug report
3. Plan fix in separate branch
4. Re-test before re-release

## Appendix: Glossary

| Term | Definition |
|------|-----------|
| Type alias | Modern C++ syntax for creating type synonyms (`using X = Y`) |
| Typedef | C syntax for creating type synonyms (`typedef Y X`) |
| TypeAliasDecl | Clang AST node representing `using X = Y` declaration |
| TypedefDecl | Clang AST node representing `typedef Y X` declaration |
| Chained alias | Type alias referring to another type alias |
| Template type alias | Type alias with template parameters (deferred to Phase 11) |
| Using directive | `using namespace X` - brings namespace into scope (not implemented) |
| Namespace alias | `namespace X = Y` - creates namespace shorthand (not implemented) |

---

**Created**: 2025-12-27
**Status**: COMPLETE ✅
**Version**: v2.13.0
**Dependencies**: Phase 48 (Namespaces)
**Estimated Effort**: 12-18 hours (actual: ~14 hours)
