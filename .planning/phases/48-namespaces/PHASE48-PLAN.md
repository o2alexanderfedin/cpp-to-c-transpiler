# Phase 48: Complete Namespace Support

**Phase**: 48 (Namespace Completion)
**Goal**: Complete namespace support with documentation, anonymous namespaces, and comprehensive testing
**Approach**: Parallel task execution with TDD validation
**Duration**: Est. 6-8 hours
**Priority**: HIGH (Ready for immediate implementation)
**Current Status**: 70% complete (basic namespace mangling working)

---

## Objective

Complete the namespace support feature by adding documentation, anonymous namespace handling with unique internal names, and comprehensive test coverage. The existing 70% implementation provides name mangling for classes, methods, functions, and scoped enums in namespaces. This phase brings the feature to 100% production readiness.

## Context

**Previous Implementation:**
- Phase 46: Scoped enums with namespace integration ✅
- Story #65: Namespace-aware name mangling ✅

**Current State:**
- NameMangler.cpp implements namespace hierarchy extraction
- Name mangling pattern: `namespace_class_method`
- 5 tests passing in NameManglerTest.cpp
- Integration with CppToCVisitor complete
- CodeGenerator emits mangled names correctly

**What Works (70%):**
- Single namespaces: `ns::func()` → `ns_func()`
- Nested namespaces: `ns1::ns2::func()` → `ns1_ns2_func()`
- Namespace classes: `ns::MyClass` → `ns_MyClass`
- Namespace methods: `ns::MyClass::method()` → `ns_MyClass_method()`
- Scoped enums in namespaces: `ns::E::A` → `ns_E__A`
- extern "C" functions: Not mangled (C linkage preserved)
- main() function: Never mangled

**What's Missing (30%):**
- Documentation (user guide, examples, FAQ)
- Anonymous namespace support (unique internal names)
- Using directives (simplified approach: document as unsupported)
- Enhanced test coverage (10+ additional test cases)
- Edge case testing (deep nesting, overloads, static methods)

**Translation Pattern:**
```cpp
// C++ Input
namespace graphics::math {
    class Vector {
        void normalize();
    };
}

// C Output
struct graphics_math_Vector { };
void graphics_math_Vector_normalize(struct graphics_math_Vector* this);
```

**Dependencies:**
- None (all prerequisites met)
- Uses existing NameMangler infrastructure
- Integrates with CppToCVisitor and CodeGenerator

---

## Tasks

### Group 1: Documentation (Parallel Execution)

**Task 1: User Documentation** (Est. 2-3 hours)
- **Owner**: Documentation specialist
- **Files**:
  - `docs/features/NAMESPACE_GUIDE.md` - User-level documentation
  - `docs/features/NAMESPACE_FAQ.md` - Common questions and answers
  - Update `docs/TRANSPILABLE_CPP.md` - Add namespace section
- **Content**:
  - What's supported (with examples)
  - What's not supported (with workarounds)
  - Naming convention explanation (ns_name pattern)
  - Common patterns and use cases
  - Migration guide from non-namespaced code
  - Integration with other features (classes, enums, methods)
- **Examples** (5+ working examples):
  - Simple namespace function
  - Nested namespace classes
  - Scoped enums in namespaces
  - Overloaded functions in namespaces
  - Static methods in namespaced classes
- **Tests**: All examples must compile and transpile
- **Verification**:
  - [ ] NAMESPACE_GUIDE.md created with 5+ examples
  - [ ] NAMESPACE_FAQ.md created with 10+ Q&A pairs
  - [ ] TRANSPILABLE_CPP.md updated
  - [ ] All examples compile (C++) and transpile (C)
  - [ ] No linter warnings
  - [ ] Linked from main README

### Group 2: Anonymous Namespace Support (Parallel Execution)

**Task 2: Anonymous Namespace Implementation** (Est. 2-3 hours)
- **Owner**: Core developer
- **Handler**: NameMangler
- **Method**: Extend `extractNamespaceHierarchy()` for anonymous namespaces
- **Implementation**:
  - Detect `NamespaceDecl::isAnonymousNamespace()`
  - Generate unique ID based on source location hash
  - Pattern: `_anon_<hash>_name` for file-local linkage
  - Ensure uniqueness across translation units
  - Handle nested anonymous namespaces
- **Algorithm**:
  ```cpp
  std::vector<std::string> NameMangler::extractNamespaceHierarchy(Decl *D) {
      std::vector<std::string> namespaces;
      DeclContext *DC = D->getDeclContext();

      while (DC) {
          if (auto *ND = dyn_cast<NamespaceDecl>(DC)) {
              if (!ND->isAnonymousNamespace()) {
                  namespaces.push_back(ND->getName().str());
              } else {
                  // Generate unique ID from source location
                  SourceLocation Loc = ND->getLocation();
                  std::string FileID = getFileID(Loc);
                  std::string uniqueId = "_anon_" + FileID;
                  namespaces.push_back(uniqueId);
              }
          }
          DC = DC->getParent();
      }
      std::reverse(namespaces.begin(), namespaces.end());
      return namespaces;
  }
  ```
- **Tests** (6-8 tests):
  - Anonymous namespace function
  - Anonymous namespace class
  - Nested anonymous namespaces
  - Anonymous namespace with scoped enum
  - Multiple anonymous namespaces in same file (unique IDs)
  - Anonymous namespace within named namespace
  - Static function in anonymous namespace
  - Global vs anonymous namespace collision avoidance
- **Verification**:
  - [ ] `extractNamespaceHierarchy()` handles anonymous namespaces
  - [ ] Unique IDs generated for each anonymous namespace
  - [ ] 6+ unit tests pass
  - [ ] No name collisions in test suite
  - [ ] C code compiles with `static` linkage where appropriate

### Group 3: Enhanced Test Coverage (Parallel Execution)

**Task 3: Comprehensive Test Suite** (Est. 2-3 hours)
- **Owner**: QA engineer
- **File**: `tests/NameManglerTest.cpp`
- **Tests** (12+ new tests):

  1. **ExternCInNamespace** - extern "C" prevents mangling even in namespace
     ```cpp
     namespace n { extern "C" void c_func(); }
     // Expected: c_func (not n_c_func)
     ```

  2. **NamespacedScopedEnum** - Scoped enum in namespace
     ```cpp
     namespace ns { enum class E { A, B }; }
     // Expected: ns_E__A, ns_E__B
     ```

  3. **DeepNesting** - 6-level deep namespace
     ```cpp
     namespace a::b::c::d::e::f { void func(); }
     // Expected: a_b_c_d_e_f_func
     ```

  4. **OverloadedNamespacedFunc** - Overloaded functions in namespace
     ```cpp
     namespace ns {
         void func(int);
         void func(double);
     }
     // Expected: ns_func_int, ns_func_double
     ```

  5. **StaticMethodInNamespace** - Static method in namespaced class
     ```cpp
     namespace ns { class C { static void m(); }; }
     // Expected: ns_C_m (no this parameter)
     ```

  6. **NamespaceTemplateClass** - Template class in namespace
     ```cpp
     namespace ns { template<typename T> class C { }; }
     // Expected: ns_C_int (after monomorphization)
     ```

  7. **InlineNamespace** - Inline namespace (detect and warn/skip)
     ```cpp
     namespace ns { inline namespace v2 { void func(); } }
     // Expected: Document as unsupported or treat as regular namespace
     ```

  8. **NestedClassInNamespace** - Nested class in namespace
     ```cpp
     namespace ns { class Outer { class Inner { }; }; }
     // Expected: ns_Outer_Inner
     ```

  9. **NamespaceAliasResolution** - Namespace alias (if Clang resolves internally)
     ```cpp
     namespace alias = ns::nested;
     alias::func();
     // Expected: ns_nested_func (if alias resolved by Clang)
     ```

  10. **ConstexprInNamespace** - Constexpr function in namespace
      ```cpp
      namespace ns { constexpr int square(int x) { return x*x; } }
      // Expected: ns_square
      ```

  11. **MultipleOverloadsInNamespace** - 3+ overloads
      ```cpp
      namespace ns {
          void f(int);
          void f(double);
          void f(int, int);
      }
      // Expected: ns_f_int, ns_f_double, ns_f_int_int
      ```

  12. **ConstructorInNamespacedClass** - Constructor mangling
      ```cpp
      namespace ns { class C { C(); C(int); }; }
      // Expected: ns_C__ctor, ns_C__ctor_1
      ```

- **Integration Tests** (5+ tests):
  - Namespace classes with virtual methods
  - Namespace classes with inheritance
  - Namespace with templates (monomorphized)
  - Cross-namespace function calls
  - Namespace with exceptions (if supported)

- **E2E Tests** (3+ tests):
  - Complete program with namespaces (compiles and runs)
  - Namespace with multiple translation units
  - Real-world use case (e.g., graphics::math library)

- **Verification**:
  - [ ] 12+ unit tests added
  - [ ] 5+ integration tests added
  - [ ] 3+ E2E tests added
  - [ ] All tests pass (100%)
  - [ ] Code coverage ≥95% for NameMangler
  - [ ] No test regressions

---

## Execution Strategy

### Parallel Execution Groups

**Group 1 (Task 1): Documentation** - 1 task
- Independent: Can write docs while code is being enhanced
- Duration: ~2.5 hours

**Group 2 (Task 2): Anonymous Namespaces** - 1 task
- Independent: Code enhancement separate from docs
- Duration: ~2.5 hours

**Group 3 (Task 3): Enhanced Tests** - 1 task
- Independent: Can write tests while docs are being written
- Duration: ~2.5 hours

**All groups can run in parallel!**

**Total Estimated Time:**
- Parallel: ~3 hours (max of all groups)
- Sequential: ~7.5 hours
- **Time Savings: ~60%**

### Task Dependencies

```
Task 1 (Documentation) ────────┐
Task 2 (Anonymous NS)   ───────┼──→ Phase 48 Complete
Task 3 (Enhanced Tests) ────────┘

All tasks are independent and can run concurrently.
```

### Deviation Rules

1. **Using Directives**: Document as "not supported" rather than implement (high complexity, low value)
2. **Namespace Aliases**: Test if Clang resolves internally; if not, document as unsupported
3. **Inline Namespaces**: Document limitations or treat as regular namespaces
4. **Anonymous Namespace Hash**: Use simple, stable hash (file path + line number)

---

## Translation Examples

### Example 1: Simple Namespace
```cpp
// C++ Input
namespace math {
    int add(int a, int b) {
        return a + b;
    }
}

// C Output
int math_add(int a, int b) {
    return a + b;
}
```

### Example 2: Nested Namespaces
```cpp
// C++ Input
namespace graphics::math {
    class Vector {
        float x, y;
    public:
        void normalize();
    };
}

// C Output
struct graphics_math_Vector {
    float x;
    float y;
};

void graphics_math_Vector_normalize(struct graphics_math_Vector* this) {
    // Implementation
}
```

### Example 3: Scoped Enum in Namespace
```cpp
// C++ Input
namespace game {
    enum class State {
        Menu,
        Playing,
        Paused
    };
}

// C Output
enum {
    game_State__Menu,
    game_State__Playing,
    game_State__Paused
};
```

### Example 4: Anonymous Namespace
```cpp
// C++ Input (file: utils.cpp)
namespace {
    void helper() {
        // Internal implementation
    }
}

void publicFunc() {
    helper();
}

// C Output
static void _anon_utils_cpp_123_helper(void) {
    // Internal implementation
}

void publicFunc(void) {
    _anon_utils_cpp_123_helper();
}
```

### Example 5: Overloaded Functions in Namespace
```cpp
// C++ Input
namespace math {
    int max(int a, int b) { return a > b ? a : b; }
    double max(double a, double b) { return a > b ? a : b; }
}

// C Output
int math_max_int_int(int a, int b) { return a > b ? a : b; }
double math_max_double_double(double a, double b) { return a > b ? a : b; }
```

---

## Success Criteria

**Functional Requirements:**
- [ ] Basic namespace mangling works (already ✅)
- [ ] Anonymous namespaces generate unique IDs
- [ ] Nested namespaces work correctly (already ✅)
- [ ] Scoped enums in namespaces work (already ✅)
- [ ] Overloaded functions in namespaces work (already ✅)
- [ ] Static methods in namespaced classes work
- [ ] extern "C" functions never mangled (already ✅)
- [ ] main() never mangled (already ✅)

**Quality Requirements:**
- [ ] 20+ new tests pass (100%)
- [ ] Total namespace tests: 25+ (5 existing + 20 new)
- [ ] Code coverage ≥95% for NameMangler
- [ ] All linters pass (zero warnings)
- [ ] No performance regression (≤1% transpilation time overhead)
- [ ] TDD followed throughout

**Documentation Requirements:**
- [ ] NAMESPACE_GUIDE.md complete with 5+ examples
- [ ] NAMESPACE_FAQ.md with 10+ Q&A pairs
- [ ] TRANSPILABLE_CPP.md updated
- [ ] All documentation examples compile and transpile
- [ ] Linked from main README.md

**Integration Requirements:**
- [ ] NameMangler integrates with CppToCVisitor (already ✅)
- [ ] CodeGenerator emits mangled names correctly (already ✅)
- [ ] No conflicts with class mangling (already ✅)
- [ ] No conflicts with method mangling (already ✅)
- [ ] No conflicts with scoped enum mangling (already ✅)

---

## Verification Steps

### Pre-Implementation Verification
1. [ ] Review `src/NameMangler.cpp` lines 126-145 (extractNamespaceHierarchy)
2. [ ] Review `tests/NameManglerTest.cpp` current 5 tests
3. [ ] Verify integration with CppToCVisitor (already working)
4. [ ] Document current coverage gaps

### Unit Test Verification (After Task 3)
```bash
cd build
ctest -R NameManglerTest --verbose
```
**Expected**: All 25+ tests PASS (5 existing + 20 new)

### Integration Test Verification (After Task 3)
```bash
# Test with real C++ program using namespaces
./cpptoc examples/namespaces.cpp --output examples/namespaces.c
gcc examples/namespaces.c -o examples/namespaces
./examples/namespaces
# Expected: Program runs correctly
```

### Documentation Verification (After Task 1)
```bash
# Check files exist and are complete
ls -la docs/features/NAMESPACE_GUIDE.md
ls -la docs/features/NAMESPACE_FAQ.md
grep "namespace" docs/TRANSPILABLE_CPP.md

# Verify all examples compile
cd docs/features/examples
for cpp in *.cpp; do
    echo "Testing $cpp..."
    ../../../cpptoc "$cpp" --output "${cpp%.cpp}.c"
    gcc "${cpp%.cpp}.c" -o "${cpp%.cpp}"
    ./"${cpp%.cpp}"
done
```
**Expected**: All examples compile and run

### Anonymous Namespace Verification (After Task 2)
```bash
# Test anonymous namespace handling
cat > test_anon.cpp << 'EOF'
namespace {
    void helper() {}
}
void test() { helper(); }
EOF

./cpptoc test_anon.cpp --output test_anon.c
grep "_anon_" test_anon.c  # Should find unique ID
gcc test_anon.c -c  # Should compile
```
**Expected**: Anonymous namespace functions get unique IDs

### Performance Verification
```bash
# Measure transpilation time with namespace-heavy code
time ./cpptoc large_namespace_program.cpp
# Expected: <1% overhead compared to non-namespace code
```

### Final Verification (Phase Complete)
```bash
# All checks
cmake --build . --target test  # All tests pass
clang-format --dry-run src/NameMangler.cpp  # Format check
clang-tidy src/NameMangler.cpp -- -I include  # Linting
git status  # Verify all files tracked
```
**Expected**: All checks pass, Phase 48 ready for release

---

## Deliverables

### Source Code
- [ ] `src/NameMangler.cpp` - Enhanced with anonymous namespace support
- [ ] `include/NameMangler.h` - Updated interface (if needed)

### Tests
- [ ] `tests/NameManglerTest.cpp` - 20+ new tests
- [ ] `tests/integration/NamespaceIntegrationTest.cpp` - 5+ integration tests
- [ ] `tests/e2e/phase48/NamespacesE2ETest.cpp` - 3+ E2E tests

### Documentation
- [ ] `docs/features/NAMESPACE_GUIDE.md` - User guide with examples
- [ ] `docs/features/NAMESPACE_FAQ.md` - FAQ document
- [ ] `docs/TRANSPILABLE_CPP.md` - Updated with namespace section
- [ ] `README.md` - Link to namespace documentation

### Planning Documents
- [ ] `.planning/phases/48-namespaces/PHASE48-PLAN.md` - This file
- [ ] `.planning/phases/48-namespaces/PHASE48-SUMMARY.md` - Execution summary
- [ ] `.planning/phases/48-namespaces/PHASE48-COMPLETE.md` - Completion doc

### Build Configuration
- [ ] `CMakeLists.txt` - Updated with new test executables (if needed)

---

## Risk Assessment

### Technical Risks

| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| Anonymous namespace hash collisions | Medium | Low | Use stable hash (file path + line number) |
| Using directives complexity | High | N/A | Document as unsupported (deliberate decision) |
| Namespace alias issues | Medium | Low | Test if Clang resolves internally |
| Performance regression | Medium | Low | Profile and optimize if needed |

### Integration Risks

| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| Conflicts with existing mangling | High | Very Low | Already integrated and working |
| Documentation out of sync | Medium | Low | Validate all examples compile |
| Test coverage gaps | Medium | Low | Comprehensive test suite |

---

## Architecture Integration

### How Namespace Mangling Works with Other Translators

**NameMangler** (Stage 2: C++ AST → C AST):
```
CppToCVisitor receives C++ AST
    │
    ├─ For each CXXRecordDecl:
    │      NameMangler.mangleClassName(RD)
    │      → Returns "ns_ClassName"
    │      → Creates C RecordDecl with mangled name
    │
    ├─ For each CXXMethodDecl:
    │      NameMangler.mangleMethodName(MD)
    │      → Returns "ns_ClassName_methodName"
    │      → Creates C FunctionDecl with mangled name
    │
    ├─ For each FunctionDecl in namespace:
    │      NameMangler.mangleFunctionName(FD)
    │      → Returns "ns_functionName"
    │      → Creates C FunctionDecl with mangled name
    │
    └─ For each EnumConstantDecl in namespace:
           NameMangler.mangleEnumConstant(ECD)
           → Returns "ns_EnumName__value"
           → Creates C EnumConstantDecl with mangled name
```

**CodeGenerator** (Stage 3: C AST → C Source):
```
CodeGenerator receives C AST
    │
    ├─ For RecordDecl:
    │      emit "struct " + RD->getNameAsString()
    │      → "struct ns_ClassName"
    │
    ├─ For FunctionDecl:
    │      emit returnType + " " + FD->getNameAsString() + "(...)"
    │      → "void ns_ClassName_methodName(...)"
    │
    └─ For EnumConstantDecl:
           emit ECD->getNameAsString()
           → "ns_EnumName__value"

No translation decisions in Stage 3 - just emit mangled names!
```

**Key Point**: All namespace mangling happens in Stage 2 (CppToCVisitor via NameMangler). Stage 3 (CodeGenerator) simply emits the already-mangled names. This maintains proper pipeline separation.

---

## Implementation Notes

### Anonymous Namespace Unique ID Generation

**Strategy**: Use source location to generate stable, unique IDs

```cpp
std::string NameMangler::getAnonymousNamespaceID(NamespaceDecl *ND) {
    SourceLocation Loc = ND->getLocation();
    SourceManager &SM = Ctx.getSourceManager();

    // Get file name
    StringRef FileName = SM.getFilename(Loc);
    std::string FileBaseName = llvm::sys::path::filename(FileName).str();

    // Get line number
    unsigned LineNum = SM.getSpellingLineNumber(Loc);

    // Generate unique ID: _anon_<filename>_<line>
    std::string uniqueId = "_anon_" + FileBaseName + "_" + std::to_string(LineNum);

    // Replace special characters in filename
    std::replace(uniqueId.begin(), uniqueId.end(), '.', '_');
    std::replace(uniqueId.begin(), uniqueId.end(), '-', '_');

    return uniqueId;
}
```

**Examples:**
- `file.cpp:15: namespace { ... }` → `_anon_file_cpp_15_`
- `utils.cpp:42: namespace { ... }` → `_anon_utils_cpp_42_`

**Benefits:**
- Stable across compilations
- Unique per file and location
- Human-readable in generated C code
- No hash collisions

### Using Directives: Why Not Supported

Using directives (`using namespace ns;`) require name resolution during translation, which adds significant complexity:

**Challenges:**
1. Must track all active `using` directives in scope
2. Must resolve unqualified names by searching all imported namespaces
3. Must handle ambiguity errors (name found in multiple namespaces)
4. Must handle nested scopes with different `using` directives
5. Clang's AST already resolved names, so we'd need to reverse-engineer

**Decision**: Document as "not supported", recommend explicit qualification

**Workaround for users:**
```cpp
// Instead of:
using namespace std;
cout << "Hello";

// Write:
std::cout << "Hello";
```

**Transpiler output:**
```c
// No "using" needed - all names already qualified
std_cout_operator_lshift(...);  // Or similar mangled name
```

---

## TDD Workflow (Per Task)

**For Task 2 (Anonymous Namespaces):**

1. **Write failing test**:
   ```cpp
   TEST_F(NameManglerTest, AnonymousNamespace) {
       const char *code = R"(
           namespace {
               void helper();
           }
       )";
       // Test that anonymous namespace function gets unique ID
   }
   ```

2. **Run test** → RED (fails because no anonymous namespace support)

3. **Implement minimal code**:
   ```cpp
   // Extend extractNamespaceHierarchy() to handle anonymous namespaces
   if (ND->isAnonymousNamespace()) {
       std::string uniqueId = getAnonymousNamespaceID(ND);
       namespaces.push_back(uniqueId);
   }
   ```

4. **Run test** → GREEN (passes)

5. **Refactor** → Keep tests green while improving code

6. **Commit** with message: "feat(namespace): Add anonymous namespace support with unique IDs"

---

## Next Steps After Completion

**Phase 49: Template Monomorphization Enhancement** - Est. 8-10 hours
- Improved template instantiation tracking
- Recursive template support
- Template specialization
- Variadic templates (basic)

**Phase 50: Exception Handling Polish** - Est. 6-8 hours
- Enhanced exception type support
- Exception specifications
- Nested try-catch blocks
- RAII integration with exceptions

---

## Success Definition

This phase is **COMPLETE** when:

1. **Functionality**
   - Basic namespace mangling works (already ✅)
   - Anonymous namespaces generate unique IDs ✅
   - All namespace features documented ✅

2. **Testing**
   - 20+ new tests added and passing
   - Total 25+ namespace tests (100% pass rate)
   - ≥95% code coverage for NameMangler

3. **Code Quality**
   - Zero linting errors
   - No performance regression (≤1% overhead)
   - TDD followed throughout
   - SOLID principles maintained

4. **Documentation**
   - NAMESPACE_GUIDE.md complete
   - NAMESPACE_FAQ.md complete
   - TRANSPILABLE_CPP.md updated
   - All examples compile and transpile
   - Linked from main README

5. **Integration**
   - No conflicts with existing features
   - All integration points verified
   - E2E tests pass

---

## Related Documents

- **NAMESPACE_SUPPORT_SUMMARY.md**: Current implementation status (70% complete)
- **NAMESPACE_MANGLING_REFERENCE.md**: Complete mangling pattern reference
- **NAMESPACE_NEXT_STEPS.md**: Original action items for this phase
- **src/NameMangler.cpp**: Core implementation (lines 126-194)
- **tests/NameManglerTest.cpp**: Existing 5 tests

---

## Rollback Strategy

If critical issues encountered:
1. Revert to previous version (git reset --hard)
2. File GitHub issue with bug report
3. Plan fix in separate branch
4. Re-test before re-merge

---

## Appendix: Glossary

| Term | Definition |
|------|-----------|
| Namespace | C++ feature for name scoping and organization |
| Name mangling | Encoding namespace hierarchy into C names |
| Anonymous namespace | Namespace with no name (file-local linkage) |
| Using directive | `using namespace ns;` (not supported) |
| Namespace alias | `namespace alias = ns;` (Clang may resolve) |
| Inline namespace | C++11 feature for versioning (limited support) |
| Qualified name | Full name with namespace: `ns::func` |
| Unqualified name | Name without namespace: `func` |

---

**Plan Status**: ✅ Ready for execution
**Next Action**: Execute all 3 tasks in parallel - Documentation, Anonymous Namespaces, Enhanced Tests
**Estimated Completion**: 6-8 hours (3 hours parallel + 1-2 hours verification + 1-2 hours integration)
