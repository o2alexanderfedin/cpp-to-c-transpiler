# Phase 53 Plan: Using Declarations and Type Aliases

**Phase**: 53 (Using Declarations)
**Prerequisite**: Phase 48 (Namespaces)
**Status**: PLANNING
**Target**: Implement C++ using declarations, type aliases, and namespace aliases

## Phase Goal

Implement complete support for C++ `using` keyword functionality, including type aliases (`using MyType = ...`), using directives (`using namespace std`), and namespace aliases (`namespace alias = original`). Generate equivalent C typedefs, handle name resolution, and ensure compatibility with existing namespace support from Phase 48.

## Using Declarations Pattern Overview

C++ `using` keyword has three main forms:
1. **Type Aliases** - `using MyType = std::vector<int>` => typedef
2. **Using Directives** - `using namespace std` => name resolution
3. **Namespace Aliases** - `namespace fs = std::filesystem` => name mapping

### Pattern Example

**C++ Source:**
```cpp
// Type aliases
using IntVector = std::vector<int>;
using IntPtr = int*;
using FuncPtr = void (*)(int, int);

// Template type aliases
template<typename T>
using Vec = std::vector<T>;

// Namespace aliases
namespace fs = std::filesystem;
namespace chrono = std::chrono;

// Using directives
using namespace std;

// Using declarations (specific names)
using std::string;
using std::cout;

// Example usage
IntVector numbers;
fs::path myPath("/tmp");
cout << "Hello" << endl;
```

**Generated C (Using Declaration Pattern):**
```c
/* Type aliases => typedef */
typedef struct vector_int IntVector;
typedef int* IntPtr;
typedef void (*FuncPtr)(int, int);

/* Template type aliases => typedef per instantiation */
typedef struct vector_int Vec_int;
typedef struct vector_float Vec_float;

/* Namespace aliases => #define or comment */
/* namespace fs = std::filesystem */
#define fs__path std__filesystem__path
#define fs__create_directory std__filesystem__create_directory

/* Using directives => fully qualified names in C */
/* using namespace std; */
/* All std:: names accessible without prefix in C++ */
/* In C: use std__ prefix explicitly */

/* Using declarations => #define or typedef */
#define string std__string
#define cout std__cout

/* Example usage - translated */
struct vector_int numbers;
struct std__filesystem__path myPath;
std__filesystem__path__init(&myPath, "/tmp");
std__cout__operator_lshift(&std__cout, "Hello");
std__cout__operator_lshift(&std__cout, std__endl);
```

## Key Concepts

### Type Aliases vs Typedef
- C++ `using` is semantically identical to `typedef` in simple cases
- Templates + using: requires monomorphization before typedef generation
- Typedef maintains type equivalence for function pointers, arrays

### Using Directives vs Using Declarations
- **Using directive** (`using namespace std`): Makes entire namespace visible
- **Using declaration** (`using std::string`): Makes specific name visible
- C doesn't have namespaces, so translation is name-based

### Namespace Aliases
- Create shorthand for long namespace names
- In C: translate to #define macros or maintain mapping table
- Must track aliased names throughout translation unit

## Implementation Tasks

### Group 1: Type Alias Detection & Translation (3 tasks - parallel)

**Task 1: Type Alias Analysis** (Est. 2-3 hours)
- Create `TypeAliasAnalyzer` helper class
- Detect `UsingDecl` and `TypeAliasDecl` in Clang AST
- Extract underlying type information
- Handle template type aliases (`UsingAliasTemplateDecl`)
- **Tests** (10-12 tests):
  - Detect simple type alias (using X = int)
  - Detect pointer type alias (using X = int*)
  - Detect reference type alias (using X = int&)
  - Detect function pointer alias
  - Detect struct/class type alias
  - Detect namespace-qualified type alias
  - Detect template type alias declaration
  - Handle forward-declared types
  - Extract correct underlying type
  - Preserve const/volatile qualifiers
  - Handle multi-level aliases (using Y = X, using X = int)

**Task 2: Typedef Generator** (Est. 2-3 hours) - PARALLEL with Task 1
- Create `TypedefGenerator` helper class
- Generate C typedef from C++ type alias
- Pattern: `typedef UnderlyingType AliasName;`
- Handle complex types (function pointers, arrays, nested templates)
- **Tests** (12-15 tests):
  - Generate simple typedef (int)
  - Generate pointer typedef
  - Generate array typedef
  - Generate function pointer typedef
  - Generate struct typedef
  - Generate nested type typedef
  - Generate const qualified typedef
  - Generate volatile qualified typedef
  - Generate template instantiation typedef
  - Preserve calling convention (if any)
  - Handle multi-word types (unsigned long long)
  - Generate forward declaration if needed

**Task 3: Template Type Alias Monomorphization** (Est. 3-4 hours) - PARALLEL with Tasks 1,2
- Extend template monomorphization to handle type aliases
- Generate typedef for each template instantiation
- Pattern: `typedef vector_T AliasName_T;`
- Track instantiations across translation unit
- **Tests** (10-12 tests):
  - Detect template type alias usage
  - Generate typedef for int instantiation
  - Generate typedef for float instantiation
  - Generate typedef for pointer instantiation
  - Generate typedef for struct instantiation
  - Handle multiple template parameters
  - Handle nested template aliases
  - Avoid duplicate typedefs
  - Generate correct mangled names
  - Integration with existing template system

### Group 2: Namespace Alias Support (2 tasks - parallel)

**Task 4: Namespace Alias Analyzer** (Est. 2-3 hours)
- Create `NamespaceAliasAnalyzer` helper class
- Detect `NamespaceAliasDecl` in Clang AST
- Build alias -> original namespace mapping
- Track alias scope (file-level, namespace-level)
- **Tests** (8-10 tests):
  - Detect namespace alias declaration
  - Extract alias name
  - Extract original namespace name
  - Handle nested namespace aliases (ns::inner)
  - Handle multi-level aliases (a = b, b = c)
  - Resolve alias chain to original
  - Track alias scope correctly
  - Handle anonymous namespace aliasing (error)
  - Detect shadowing of aliases

**Task 5: Namespace Alias Translation** (Est. 2-3 hours) - PARALLEL with Task 4
- Extend `NameHandler` to translate aliased names
- Replace alias prefix with original namespace prefix
- Pattern: `alias__name` => `original__namespace__name`
- Generate #define macros or comment documentation
- **Tests** (10-12 tests):
  - Translate simple alias usage (fs::path)
  - Replace alias with original namespace
  - Handle function calls through alias
  - Handle type references through alias
  - Handle variable references through alias
  - Generate #define for alias
  - Multiple aliases in same file
  - Nested namespace alias (alias::inner::name)
  - Alias in template context
  - Alias in function signature

### Group 3: Using Directive Support (3 tasks - 2 parallel + 1)

**Task 6: Using Directive Analyzer** (Est. 2-3 hours)
- Create `UsingDirectiveAnalyzer` helper class
- Detect `UsingDirectiveDecl` in Clang AST
- Track active using directives per scope
- Build name lookup table for unqualified names
- **Tests** (8-10 tests):
  - Detect using directive (using namespace X)
  - Track directive scope (file, namespace, function)
  - Handle multiple using directives
  - Handle nested namespace using directives
  - Detect namespace not found (error)
  - Track directive order (shadowing)
  - Handle using directive in header
  - Scope-based directive activation/deactivation

**Task 7: Unqualified Name Resolution** (Est. 3-4 hours) - PARALLEL with Task 6
- Extend `ExpressionHandler` to resolve unqualified names
- Check active using directives for name lookup
- Generate fully qualified C name from unqualified C++ name
- Pattern: `cout` => `std__cout` (if `using namespace std` active)
- **Tests** (12-15 tests):
  - Resolve unqualified variable name
  - Resolve unqualified function name
  - Resolve unqualified type name
  - Resolve with single using directive
  - Resolve with multiple using directives
  - Ambiguous name resolution (error)
  - Qualified name bypasses using directive
  - Name resolution in nested scopes
  - Using directive doesn't affect qualified names
  - Function overload resolution with using
  - Template name resolution with using
  - ADL (Argument-Dependent Lookup) interaction

**Task 8: Using Declaration Support** (Est. 2-3 hours) - DEPENDS on Tasks 6, 7
- Handle `UsingDecl` for specific names (`using std::string`)
- Generate #define or maintain name mapping
- Pattern: `#define string std__string`
- Integrate with unqualified name resolution
- **Tests** (8-10 tests):
  - Detect using declaration (using X::name)
  - Generate #define for using declaration
  - Resolve unqualified name via using declaration
  - Multiple using declarations
  - Using declaration shadows previous name
  - Using declaration in namespace
  - Using declaration in class (inherit ctor)
  - Using declaration conflicts (error)

### Group 4: Integration & Edge Cases (2 tasks - sequential)

**Task 9: Integration with Existing Systems** (Est. 3-4 hours)
- Integrate with Phase 48 namespace support
- Ensure typedef generation doesn't conflict
- Update `NameHandler` for alias resolution
- Update `TypeHandler` for typedef lookup
- **Tests** (15-18 tests):
  - Type alias with namespace qualified type
  - Namespace alias with namespaced types
  - Using directive with namespaced functions
  - Template type alias with namespaced template
  - Multiple translation units with aliases
  - Header file with type aliases
  - Forward declaration with type alias
  - Function parameter with type alias
  - Return type with type alias
  - Member variable with type alias
  - Static variable with type alias
  - Global variable with type alias
  - Type alias in template specialization
  - Recursive type alias (error detection)
  - Circular namespace alias (error detection)

**Task 10: Documentation & Examples** (Est. 2 hours) - SEQUENTIAL after Task 9
- Document using declaration support
- Create user-facing guide
- Migration examples (C++ => C)
- Known limitations
- **Deliverables**:
  - `.planning/phases/53-using-declarations/PHASE53-USAGE-GUIDE.md`
  - Example code snippets in comments
  - Test cases as documentation
  - Update main README with Phase 53 status

### Group 5: End-to-End Testing (1 task)

**Task 11: E2E Tests** (Est. 3-4 hours)
- Create `tests/e2e/phase53/UsingDeclarationsE2ETest.cpp`
- Compile and execute generated C code
- **Tests** (12-15 tests):
  - 2 active sanity tests
  - 3-4 active tests (realistic usage)
  - 8-10 disabled complex algorithm tests:
    - Type alias with STL containers
    - Namespace alias with filesystem operations
    - Using directive with stream operations
    - Template type alias with smart pointers
    - Using declarations in class hierarchy
    - Mixed using forms in single file
    - Type alias with function pointers
    - Namespace alias in template context
    - Using directive with operator overloading
    - Chained namespace aliases

## Execution Strategy

### Parallel Execution Groups

**Group 1 (Tasks 1-3)**: Type Alias Detection & Translation
- All 3 tasks in parallel - ~3-4 hours
- **Total: ~3-4 hours**

**Group 2 (Tasks 4-5)**: Namespace Alias Support
- Both tasks in parallel - ~2-3 hours
- **Total: ~2-3 hours**

**Group 3 (Tasks 6-8)**: Using Directive Support
- Task 6 + Task 7 in parallel - ~3-4 hours
- Task 8 sequential after 6,7 - ~2-3 hours
- **Total: ~5-7 hours**

**Group 4 (Tasks 9-10)**: Integration & Edge Cases
- Task 9 then Task 10 sequential - ~5-6 hours
- **Total: ~5-6 hours**

**Group 5 (Task 11)**: E2E Testing
- Task 11 - ~3-4 hours
- **Total: ~3-4 hours**

**Overall Estimated Time:**
- Parallel: ~18-24 hours
- Sequential: ~25-35 hours
- **Time Savings: ~30-35%**

## Files to Create

1. `include/handlers/TypeAliasAnalyzer.h` - Analyze type aliases
2. `src/handlers/TypeAliasAnalyzer.cpp` - Implementation
3. `tests/unit/handlers/TypeAliasAnalyzerTest.cpp` - Unit tests
4. `include/handlers/TypedefGenerator.h` - Generate C typedefs
5. `src/handlers/TypedefGenerator.cpp` - Implementation
6. `tests/unit/handlers/TypedefGeneratorTest.cpp` - Unit tests
7. `include/handlers/NamespaceAliasAnalyzer.h` - Analyze namespace aliases
8. `src/handlers/NamespaceAliasAnalyzer.cpp` - Implementation
9. `tests/unit/handlers/NamespaceAliasAnalyzerTest.cpp` - Unit tests
10. `include/handlers/UsingDirectiveAnalyzer.h` - Analyze using directives
11. `src/handlers/UsingDirectiveAnalyzer.cpp` - Implementation
12. `tests/unit/handlers/UsingDirectiveAnalyzerTest.cpp` - Unit tests
13. `tests/e2e/phase53/UsingDeclarationsE2ETest.cpp` - E2E tests
14. `.planning/phases/53-using-declarations/PHASE53-USAGE-GUIDE.md` - User guide
15. `.planning/phases/53-using-declarations/PHASE53-COMPLETE.md` - Summary doc

## Files to Modify

1. `include/handlers/TypeHandler.h` - Add typedef lookup
2. `src/handlers/TypeHandler.cpp` - Implement typedef resolution
3. `include/handlers/NameHandler.h` - Add alias name resolution
4. `src/handlers/NameHandler.cpp` - Implement alias mapping
5. `include/handlers/ExpressionHandler.h` - Add unqualified name resolution
6. `src/handlers/ExpressionHandler.cpp` - Implement using directive lookup
7. `include/CppToCVisitor.h` - Add using declaration handling
8. `src/CppToCVisitor.cpp` - Integrate analyzers
9. `CMakeLists.txt` - Add new test targets

## Success Criteria

- [ ] All 80-90 unit tests pass (100%)
- [ ] All 15-18 integration tests pass (100%)
- [ ] 2-4 E2E active tests pass (100%)
- [ ] Type aliases generate correct typedefs
- [ ] Namespace aliases resolve to original namespaces
- [ ] Using directives enable unqualified name resolution
- [ ] Using declarations create name mappings
- [ ] Template type aliases monomorphize correctly
- [ ] No conflicts with existing typedef/namespace systems
- [ ] Generated C code compiles without warnings
- [ ] Code follows SOLID principles
- [ ] TDD followed throughout

## Test Count Targets

- **Group 1 Tests**: 32-39 tests (Alias Analysis 10-12, Typedef Gen 12-15, Template Mono 10-12)
- **Group 2 Tests**: 18-22 tests (Namespace Alias Analyzer 8-10, Translation 10-12)
- **Group 3 Tests**: 28-35 tests (Directive Analyzer 8-10, Name Resolution 12-15, Using Decl 8-10)
- **Group 4 Tests**: 15-18 tests (Integration 15-18)
- **Group 5 Tests**: 12-15 tests (E2E)
- **Total: 105-129 tests** (target 60-80 active, rest can be disabled for complex scenarios)

## Dependencies

**Requires:**
- Phase 48 (Namespaces) - MUST BE COMPLETE
- NameHandler - namespace name mangling
- TypeHandler - type resolution
- TemplateMonomorphizer - template instantiation
- ExpressionHandler - name resolution
- Clang AST traversal infrastructure

**External:**
- Clang AST API for using declarations
- Clang UsingDecl, TypeAliasDecl, NamespaceAliasDecl
- Clang UsingDirectiveDecl
- Google Test framework
- CMake build system

## Risk Mitigation

**Risk 1: Name Resolution Ambiguity**
- Mitigation: Implement C++ name lookup rules faithfully
- Fallback: Error on ambiguous names (better than silent bugs)
- Test: Comprehensive ambiguity detection tests

**Risk 2: Template Type Alias Complexity**
- Mitigation: Leverage existing template monomorphization
- Test: Integration with template system
- Document: Known limitations with dependent types

**Risk 3: Using Directive Scope Complexity**
- Mitigation: Track scope carefully with AST context
- Test: Nested scope tests, shadowing tests
- Fallback: Conservative approach (require qualification)

**Risk 4: Interaction with Phase 48 Namespaces**
- Mitigation: Design alias system to extend, not replace
- Test: Integration tests with Phase 48
- Review: Code review by namespace expert

## Translation Patterns

### Type Alias Translation

```cpp
// C++ Input
using IntPtr = int*;
using Callback = void (*)(int);

// C Output
typedef int* IntPtr;
typedef void (*Callback)(int);
```

### Namespace Alias Translation

```cpp
// C++ Input
namespace fs = std::filesystem;
fs::path p("/tmp");

// C Output
/* namespace fs = std::filesystem */
struct std__filesystem__path p;
std__filesystem__path__init(&p, "/tmp");
```

### Using Directive Translation

```cpp
// C++ Input
using namespace std;
cout << "Hello" << endl;

// C Output
/* using namespace std; */
std__cout__operator_lshift(&std__cout, "Hello");
std__cout__operator_lshift(&std__cout, std__endl);
```

### Using Declaration Translation

```cpp
// C++ Input
using std::string;
string s = "hello";

// C Output
/* using std::string; */
struct std__string s;
std__string__init_cstr(&s, "hello");
```

## Known Limitations

1. **ADL (Argument-Dependent Lookup)** - May not fully replicate C++ ADL semantics
2. **Template Dependent Names** - Complex dependent type aliases may need manual intervention
3. **Using Directive in Headers** - May cause name pollution in generated C code
4. **Circular Aliases** - Detected and reported as error (C++ would also error)
5. **Using in Class Scope** - Inheriting constructors not fully supported (defer to later phase)

## Next Steps After Completion

**Phase 54: Range-Based For Loops** - Est. 20-30 hours
- Dependency on iterators and auto type deduction
- `for (auto x : container)` translation
- Iterator protocol implementation

**Phase 55: Friend Declarations** - Est. 8-12 hours
- Friend classes and functions
- Access control bypass
- Low priority

## References

### Using Declarations
- [C++ Reference: Type Alias](https://en.cppreference.com/w/cpp/language/type_alias)
- [C++ Reference: Using Declaration](https://en.cppreference.com/w/cpp/language/using_declaration)
- [C++ Reference: Namespace Alias](https://en.cppreference.com/w/cpp/language/namespace_alias)

### Technical Resources
- [Clang UsingDecl Documentation](https://clang.llvm.org/doxygen/classclang_1_1UsingDecl.html)
- [Clang TypeAliasDecl Documentation](https://clang.llvm.org/doxygen/classclang_1_1TypeAliasDecl.html)
- [Clang NamespaceAliasDecl Documentation](https://clang.llvm.org/doxygen/classclang_1_1NamespaceAliasDecl.html)

---

**Created**: 2025-12-26
**Status**: READY FOR IMPLEMENTATION
**Dependencies**: Phase 48 (Namespaces) MUST BE COMPLETE
**Estimated Effort**: 12-18 hours (parallel execution)
