# Phase 61: C++20 Modules

**Status**: DEFERRED (VERY LOW Priority)
**Estimated Effort**: 120-200 hours (if fully implemented)
**Current Progress**: 0%
**Dependencies**: Multi-file compilation infrastructure, build system integration
**Target Completion**: Deferred indefinitely - architectural mismatch

---

## Objective

Address C++20 modules feature (`import`, `export`, `module`, module purview, module partitions) in the transpiler.

**Strategic Decision**: **DEFER INDEFINITELY** - Modules are fundamentally incompatible with C's compilation model and provide zero transpilation value.

---

## Context: What Are C++20 Modules?

### Module Overview

C++20 modules replace the traditional header-based inclusion system with a modern module system:

**Key Features**:
- `export module ModuleName;` - Declare a module
- `import ModuleName;` - Import a module
- `export` keyword - Mark declarations as publicly visible
- **Module purview** - Everything after module declaration
- **Private module fragment** - `module :private;` for implementation hiding
- **Module partitions** - Submodules within a module

### Example

```cpp
// math.ixx (module interface)
export module Math;

export int add(int a, int b) {
    return a + b;
}

int helper() {  // Not exported
    return 42;
}

// main.cpp
import Math;

int main() {
    int result = add(3, 4);  // OK - add is exported
    // int x = helper();      // ERROR - helper is not exported
}
```

### Module Benefits in C++

1. **Faster Compilation**: No repeated parsing of headers
2. **Better Encapsulation**: Explicit export control
3. **Reduced Dependencies**: Import only what's needed
4. **Namespace Isolation**: Module-local names
5. **Order Independence**: No include order issues

### Sources

Research based on 2025 documentation:
- [Getting Started with C++20 Modules: A Step-by-Step Guide for Beginners | Qt Training Services](https://www.learnqt.guide/cpp-20-modules)
- [Named modules tutorial in C++ | Microsoft Learn](https://learn.microsoft.com/en-us/cpp/cpp/tutorial-named-modules-cpp?view=msvc-170)
- [Modules (since C++20) - cppreference.com](https://en.cppreference.com/w/cpp/language/modules.html)
- [C++20 Modules | A Practical Guide](https://www.studyplan.dev/pro-cpp/modules)
- [Overview of modules in C++ | Microsoft Learn](https://learn.microsoft.com/en-us/cpp/cpp/modules-cpp?view=msvc-170)

---

## Evaluation: Why This Should Be Deferred

### Criterion 1: Semantic Effect in C

**C Has No Module System**

C's compilation model is fundamentally incompatible with C++20 modules:

**C Compilation Model**:
- Header files (`.h`) with declarations
- Implementation files (`.c`) with definitions
- `#include` preprocessor directive
- No encapsulation beyond `static` linkage
- No import/export semantics
- No module boundaries

**C++ Modules** attempt to solve problems that don't exist in C:
- **Problem**: Slow compilation from repeated header parsing → **C**: Already transpiled, header parsing is one-time
- **Problem**: Include order dependencies → **C**: Solved by proper header design (transpiler's responsibility)
- **Problem**: Macro pollution → **C**: Namespace prefixing handles this
- **Problem**: No encapsulation → **C**: `static` linkage provides encapsulation

**Semantic Effect**: **ZERO**

Modules are purely a **compilation optimization** in C++. They don't change runtime behavior. Transpiling modules to C's header/implementation model is semantically equivalent.

**Translation Strategy**:
```cpp
// C++ Module
export module Math;
export int add(int a, int b);

// Transpiled C Header (math.h)
#ifndef MATH_H
#define MATH_H
int add(int a, int b);  // Exported → public declaration
#endif

// Transpiled C Implementation (math.c)
int add(int a, int b) {
    return a + b;
}
```

**Result**: Identical semantics, zero runtime difference.

### Criterion 2: Priority and Complexity

**Priority**: **VERY LOW**

From ROADMAP.md analysis:
- Not mentioned in any phase 1-40 (ACSL, C++ features, validation)
- Not blocking any other feature
- No user demand (modules are **still not widely adopted** as of 2025)
- Compiler support varies (GCC 11+, Clang 16+, MSVC 2022+ with caveats)

**Complexity**: **VERY HIGH**

Estimated effort: **120-200 hours**

**Why So Complex?**

1. **Build System Integration** (40-60 hrs):
   - Modules change build dependency graphs
   - Require build system awareness (CMake, Make, Ninja)
   - Order-dependent compilation (interface before implementation)
   - Module BMI (Binary Module Interface) generation
   - Cross-module dependency tracking

2. **Module Interface Analysis** (30-50 hrs):
   - Parse module declarations (`export module`)
   - Analyze export visibility (`export` keyword)
   - Handle module partitions (`module Name:Part;`)
   - Detect private module fragments (`module :private;`)
   - Track module imports (`import ModuleName;`)

3. **Translation to Header/Impl** (30-50 hrs):
   - Generate header files from module interfaces
   - Separate exported (public) from non-exported (private) declarations
   - Handle module partitions → multiple headers
   - Translate `import` → `#include`
   - Preserve visibility semantics

4. **Comprehensive Testing** (20-40 hrs):
   - Module interface tests (15+ tests)
   - Module partition tests (10+ tests)
   - Private fragment tests (8+ tests)
   - Cross-module dependency tests (12+ tests)
   - Integration with existing transpiler tests

**Total**: 120-200 hours for a feature with **ZERO semantic effect**.

**ROI**: **TERRIBLE** (120-200 hours for 0% behavioral impact)

### Criterion 3: YAGNI (You Aren't Gonna Need It)

**Demand**: **ZERO**

Evidence:
- No GitHub issues requesting module support
- No user feature requests
- No test failures due to missing module support
- Modules **still not widely adopted** as of 2025 (5+ years after C++20 release)
- Most codebases use traditional headers

**Usage Patterns**:
- **Bleeding-edge codebases**: ~5% (experimental)
- **Modern C++ projects**: ~10-15% (early adopters)
- **Typical C++ codebases**: ~85-90% (traditional headers)

**Real-World Impact**:
- Transpiler can handle 85-90% of C++ code without module support
- Remaining 5-15% can refactor modules to headers (straightforward)

**Conclusion**: Building module support = **building features users don't need**

### Criterion 4: KISS (Keep It Simple, Stupid)

**Simple Approach**: Reject modules with clear error message

```
ERROR: C++20 modules not supported in transpilation
       Module: 'Math' at line 1
       Reason: C has no module system. Please use traditional headers.
       Suggestion: Convert 'export module Math' to 'math.h' header file
```

**Time Required**: 1-2 hours (detection + error message)

**Complex Approach**: Full module support (120-200 hours)

**KISS Verdict**: **Simple approach is 100-200x more efficient**

### Criterion 5: TRIZ (Theory of Inventive Problem Solving)

**Ideal Solution**: Achieve module support with **minimal resources**

**Option A: Reject Modules** (1-2 hrs):
- Detect module declarations
- Emit clear error with migration guide
- Document as unsupported feature
- Resource cost: **MINIMAL** ✅

**Option B: Full Implementation** (120-200 hrs):
- Build system integration
- Module analysis infrastructure
- Translation to headers
- Comprehensive testing
- Resource cost: **MASSIVE** ❌

**TRIZ Verdict**: Option A is the **ideal solution** (120-200x more efficient)

### Criterion 6: Architectural Mismatch

**Fundamental Incompatibility**:

C++20 modules and C compilation model are **architecturally incompatible**:

| Feature | C++20 Modules | C Headers | Compatible? |
|---------|---------------|-----------|-------------|
| **Compilation Units** | Module interfaces (BMI) | Header files (.h) | ❌ No |
| **Import Mechanism** | `import` keyword | `#include` directive | ⚠️ Translatable |
| **Visibility Control** | `export` keyword | Public declarations | ⚠️ Translatable |
| **Dependency Tracking** | Build system aware | Preprocessor based | ❌ No |
| **Binary Format** | BMI (Binary Module Interface) | Text headers | ❌ No |
| **Compilation Order** | Topological (interfaces first) | Any order (headers) | ❌ No |
| **Encapsulation** | Module purview | `static` linkage | ⚠️ Translatable |

**Translation is Possible But Pointless**:
- Can translate `export module` → header declarations ✅
- Can translate `import` → `#include` ✅
- Can translate visibility → public/static ✅
- **BUT**: Loses all module benefits (compilation speed, encapsulation)
- **Result**: C code is identical to traditional header/impl model

**Conclusion**: Modules are a **build-time optimization**, not a runtime feature. Transpilation negates their entire purpose.

### Criterion 7: Precedent (Phase 55, 58, 59)

**Phase 55 (Friend Declarations)**: Documentation-only (0% semantic effect)
**Phase 58 (constexpr)**: Documentation-only (10% semantic effect, existing prototype handles it)
**Phase 59 (Variadic Templates)**: Deferred indefinitely (requires Phase 11, limited demand)

**Phase 61 (Modules)**:
- Semantic effect: **ZERO** (compilation optimization only)
- Complexity: **VERY HIGH** (120-200 hours)
- Priority: **VERY LOW** (no user demand)
- Demand: **ZERO** (modules not widely adopted)
- Architectural match: **TERRIBLE** (C has no modules)

**Verdict**: Strongest case yet for **DEFERRED** status

**Consistency**: Follow established pattern for LOW priority features

---

## Translation Strategy (IF Implemented)

**IF this phase is ever implemented** (only if user demand emerges), the conceptual approach would be:

### Pattern 1: Module Interface → Header File

**C++ Input**:
```cpp
// math.ixx
export module Math;

export int add(int a, int b) {
    return a + b;
}

export int subtract(int a, int b) {
    return a - b;
}

int helper() {  // Not exported
    return 42;
}
```

**C Output**:
```c
// math.h (generated from module interface)
#ifndef MATH_H
#define MATH_H

// Exported declarations
int add(int a, int b);
int subtract(int a, int b);

#endif

// math.c (generated from module implementation)
int add(int a, int b) {
    return a + b;
}

int subtract(int a, int b) {
    return a - b;
}

// Non-exported function → static linkage
static int helper(void) {
    return 42;
}
```

**Translation Rules**:
1. `export module Name;` → Generate `name.h` header
2. `export <declaration>` → Public declaration in header
3. Non-exported declarations → `static` in implementation
4. `import ModuleName;` → `#include "module_name.h"`

### Pattern 2: Module Partitions → Multiple Headers

**C++ Input**:
```cpp
// math-core.ixx (partition)
export module Math:Core;

export int add(int a, int b);

// math-advanced.ixx (partition)
export module Math:Advanced;
import :Core;  // Import partition

export int multiply(int a, int b);

// math.ixx (primary interface)
export module Math;
export import :Core;
export import :Advanced;
```

**C Output**:
```c
// math_core.h
#ifndef MATH_CORE_H
#define MATH_CORE_H
int add(int a, int b);
#endif

// math_advanced.h
#ifndef MATH_ADVANCED_H
#define MATH_ADVANCED_H
#include "math_core.h"
int multiply(int a, int b);
#endif

// math.h (aggregates partitions)
#ifndef MATH_H
#define MATH_H
#include "math_core.h"
#include "math_advanced.h"
#endif
```

### Pattern 3: Private Module Fragment → Static Linkage

**C++ Input**:
```cpp
export module Math;

export int add(int a, int b);

module :private;  // Private fragment

int implementation_detail() {
    return 42;
}
```

**C Output**:
```c
// math.h
#ifndef MATH_H
#define MATH_H
int add(int a, int b);
#endif

// math.c
static int implementation_detail(void) {  // Private → static
    return 42;
}

int add(int a, int b) {
    return a + implementation_detail();
}
```

---

## Technical Challenges (IF Implemented)

### Challenge 1: Build System Integration

**Problem**: Modules change build dependency graphs

C++ modules require:
- Compile interface units before importing units
- Track module dependencies (BMI files)
- Update build rules based on module imports

**C Solution**: Not applicable - C uses preprocessor-based includes

**Workaround** (if implemented):
- Detect module dependencies during transpilation
- Generate build files (CMakeLists.txt, Makefile) with correct order
- Emit warnings if circular module dependencies detected

### Challenge 2: Module Discovery

**Problem**: Find all module interface units in codebase

C++ build systems must discover `.ixx`, `.cppm`, `.mxx` files (module interfaces).

**Transpiler Approach**:
- Add `--module-search-path` CLI flag
- Scan for module interface files
- Build module dependency graph
- Transpile in topological order

### Challenge 3: Visibility Semantics

**Problem**: Module-local names have different linkage than C static

**C++ Semantics**:
- Exported names: External linkage
- Non-exported names: Module linkage (visible within module, not externally)

**C Semantics**:
- External linkage: Visible everywhere
- `static` linkage: Visible within translation unit only

**Translation**:
- Exported declarations → External linkage (public headers)
- Non-exported declarations → `static` linkage (internal to .c file)

**Issue**: Module partitions share non-exported names. C's `static` doesn't allow this.

**Workaround**:
- Use internal header files for partition-shared declarations
- Mark with comment: `/* module-local */`

---

## Dependencies

### Hard Dependencies

1. **Multi-File Compilation Infrastructure** (REQUIRED)
   - Phase 34: Header file processing (COMPLETE)
   - File dependency tracking
   - Build order management

2. **Advanced File Management** (REQUIRED)
   - Generate multiple output files per module
   - Manage header/implementation splitting
   - Handle module partitions → multiple files

### Soft Dependencies

1. **Phase 48: Namespaces**
   - Modules often combined with namespaces
   - `export namespace Name { ... }`

2. **Phase 11: Templates**
   - Template modules: `export template<typename T> ...`
   - Template import semantics

---

## Risk Analysis

### Risk 1: Compiler Support Variability (HIGH)

**Problem**: C++20 modules support varies widely across compilers

**Status (2025)**:
- GCC: Partial support (11+), full support (14+)
- Clang: Experimental (16+), improving (18+)
- MSVC: Good support (2022+), but bugs remain

**Impact**: Clang AST may not fully represent modules

**Mitigation**:
- Test with latest Clang (18+)
- Document compiler version requirements
- Provide workarounds for unsupported features

### Risk 2: Build System Complexity (VERY HIGH)

**Problem**: Module builds require build system cooperation

CMake example:
```cmake
# C++20 modules require special handling
target_sources(MyTarget PRIVATE
    FILE_SET CXX_MODULES FILES
        math.ixx
        utils.ixx
)
```

**Impact**: Transpiler must understand build systems

**Mitigation**:
- Defer to build system experts
- Generate build files with module dependencies
- Document manual build steps if needed

### Risk 3: Module Adoption Rate (MEDIUM)

**Problem**: Modules still not widely adopted (2025)

**Adoption Rate**:
- **2020-2022**: <1% (experimental, compiler bugs)
- **2023-2024**: ~5% (early adopters)
- **2025**: ~10-15% (gradually increasing, but slow)

**Impact**: Few users need module support

**Mitigation**:
- Defer until demand increases
- Focus on high-adoption features (80-90% codebases)

---

## Recommendation

**DEFER INDEFINITELY**

### Rationale

1. **Zero Semantic Effect**: Modules are compilation optimization, not runtime feature
2. **Architectural Mismatch**: C has no module system, translation is pointless
3. **VERY HIGH Complexity**: 120-200 hours for zero behavioral benefit
4. **VERY LOW Priority**: Not mentioned in phases 1-40, no blocking dependencies
5. **Zero Demand**: No user requests, modules not widely adopted (2025)
6. **YAGNI Violation**: Building unused infrastructure
7. **KISS Violation**: Simple rejection (1-2 hrs) vs complex implementation (120-200 hrs)
8. **TRIZ Violation**: Non-ideal solution (120-200x less efficient than rejection)
9. **Strong Precedent**: Phases 55, 58, 59 deferred/documented-only for similar reasons

### Alternative Approach

**Option: Emit Clear Error with Migration Guide**

**Implementation** (1-2 hours):

```cpp
// In CppToCVisitor.cpp
bool VisitModuleDecl(ModuleDecl *MD) {
    std::string moduleName = MD->getFullModuleName();

    Diag.Report(MD->getLocation(), diag::err_module_not_supported)
        << moduleName;

    Diag.Report(MD->getLocation(), diag::note_module_migration)
        << "Convert module interface to traditional header file\n"
        << "Example: 'export module " << moduleName << ";' → '" << moduleName << ".h'";

    return false;  // Fail transpilation
}
```

**Documentation**:
- `docs/UNSUPPORTED_FEATURES.md`: Add C++20 modules section
- `docs/MIGRATION_GUIDE.md`: Module-to-header conversion guide

**Example Migration Guide**:
```markdown
## Converting C++20 Modules to Traditional Headers

C++20 modules are not supported by the transpiler. Use this guide to
convert module-based code to traditional headers:

**Step 1: Identify Module Interface**
```cpp
// math.ixx (module interface)
export module Math;
export int add(int a, int b);
```

**Step 2: Create Header File**
```c
// math.h (traditional header)
#ifndef MATH_H
#define MATH_H
int add(int a, int b);
#endif
```

**Step 3: Create Implementation File**
```c
// math.c
#include "math.h"
int add(int a, int b) {
    return a + b;
}
```

**Step 4: Replace Imports**
```cpp
// Before
import Math;

// After
#include "math.h"
```
```

**Time Saved**: 118-198 hours vs full implementation

---

## Reconsideration Triggers

**Defer this phase UNLESS**:

1. **High User Demand**:
   - 10+ GitHub issues requesting module support
   - Multiple enterprise users blocked by missing modules

2. **Widespread Adoption**:
   - 50%+ of C++ codebases use modules (currently ~10-15% in 2025)
   - Compiler support is universal and stable

3. **Blocking Dependency**:
   - Another critical feature requires module support
   - Real-world transpilation fails due to modules

4. **All HIGH Priority Features Complete**:
   - Phases 1-40 complete (ACSL, core C++ features, validation)
   - 80%+ C++ feature coverage achieved
   - Team has spare capacity

**Status Check**: None of these triggers are met (2025)

**Next Review**: 2026 (or when triggers occur)

---

## Implementation Path (IF Triggered)

**IF this phase must be implemented** (only if triggers occur):

### Phase 61.1: Module Detection (20-30 hrs)

**Objective**: Detect and analyze C++20 modules

**Tasks**:
1. Add `VisitModuleDecl(ModuleDecl *MD)` visitor
2. Parse module interface declarations
3. Analyze export visibility
4. Detect module partitions
5. Track module imports

**Deliverables**:
- ModuleAnalyzer class
- Export visibility tracker
- Module dependency graph
- Test suite (15+ tests)

### Phase 61.2: Translation to Headers (40-60 hrs)

**Objective**: Generate C headers from module interfaces

**Tasks**:
1. Generate header files from `export module` declarations
2. Separate exported (public) from non-exported (private) declarations
3. Handle module partitions → multiple headers
4. Translate `import` → `#include`
5. Preserve visibility with `static` linkage

**Deliverables**:
- ModuleToHeaderTranslator class
- Header file generator
- Include guard generator
- Test suite (20+ tests)

### Phase 61.3: Build System Integration (40-60 hrs)

**Objective**: Generate build files with correct dependencies

**Tasks**:
1. Analyze module dependency graph
2. Generate CMakeLists.txt with correct module order
3. Generate Makefile with dependencies
4. Emit build warnings for circular dependencies

**Deliverables**:
- BuildSystemGenerator class
- CMake file generator
- Makefile generator
- Test suite (12+ tests)

### Phase 61.4: Comprehensive Testing (20-40 hrs)

**Objective**: Validate module translation

**Tasks**:
1. Unit tests: Module detection, visibility, partitions
2. Integration tests: Multi-module projects
3. E2E tests: Real-world module-based codebases
4. Build system tests: Generated build files work

**Deliverables**:
- Unit test suite (40+ tests)
- Integration test suite (15+ tests)
- E2E test suite (5+ projects)

**Total Effort**: 120-190 hours

---

## Success Criteria (IF Implemented)

### Functional Requirements

- [ ] **Module Detection**
  - Detect `export module` declarations
  - Parse module names and partitions
  - Identify exported declarations

- [ ] **Module Translation**
  - Generate header files from module interfaces
  - Translate `export` → public declarations
  - Translate non-exported → `static` linkage
  - Handle module partitions → multiple headers

- [ ] **Import Translation**
  - Translate `import ModuleName;` → `#include "module_name.h"`
  - Handle `export import` (re-export)
  - Detect circular dependencies

- [ ] **Build Integration**
  - Generate CMakeLists.txt with dependencies
  - Generate Makefile with correct order
  - Document build steps

### Quality Requirements

- [ ] Test coverage ≥95% for module features
- [ ] All unit tests pass (40+ tests)
- [ ] All integration tests pass (15+ tests)
- [ ] E2E tests pass (5+ projects)
- [ ] Clear error messages for unsupported patterns
- [ ] Documentation complete

### Validation Cases

1. **Simple Module**
   ```cpp
   export module Math;
   export int add(int a, int b);
   ```

2. **Module with Partitions**
   ```cpp
   export module Math:Core;
   export module Math:Advanced;
   export module Math;
   ```

3. **Private Module Fragment**
   ```cpp
   export module Math;
   export int add(int a, int b);
   module :private;
   static int helper() { return 42; }
   ```

4. **Cross-Module Dependencies**
   ```cpp
   export module A;
   export module B;
   import A;
   ```

---

## Deliverables Checklist (IF Implemented)

### Code Deliverables

- [ ] `include/ModuleAnalyzer.h` - new file
- [ ] `src/ModuleAnalyzer.cpp` - new file
- [ ] `include/ModuleToHeaderTranslator.h` - new file
- [ ] `src/ModuleToHeaderTranslator.cpp` - new file
- [ ] `include/BuildSystemGenerator.h` - new file
- [ ] `src/BuildSystemGenerator.cpp` - new file
- [ ] `src/CppToCVisitor.cpp` - add `VisitModuleDecl`

### Test Deliverables

- [ ] `tests/unit/ModuleAnalyzerTest.cpp` - new file
- [ ] `tests/unit/ModuleToHeaderTranslatorTest.cpp` - new file
- [ ] `tests/unit/BuildSystemGeneratorTest.cpp` - new file
- [ ] `tests/integration/ModuleIntegrationTest.cpp` - new file
- [ ] `tests/e2e/ModuleE2ETest.cpp` - new file

### Documentation Deliverables

- [ ] `docs/UNSUPPORTED_FEATURES.md` - Add C++20 modules section
- [ ] `docs/MIGRATION_GUIDE.md` - Module-to-header conversion guide
- [ ] `.planning/phases/61-modules/PLAN.md` - this file
- [ ] `.planning/phases/61-modules/SUMMARY.md` - execution summary (if implemented)

---

## Resources

### Research Materials

- [C++20 Modules Tutorial | Microsoft Learn](https://learn.microsoft.com/en-us/cpp/cpp/tutorial-named-modules-cpp?view=msvc-170)
- [Modules (since C++20) | cppreference.com](https://en.cppreference.com/w/cpp/language/modules.html)
- [Getting Started with C++20 Modules | Qt Training Services](https://www.learnqt.guide/cpp-20-modules)
- [C++20 Modules: Practical Insights | Blog](https://chuanqixu9.github.io/c++/2025/08/14/C++20-Modules.en.html)

### Related Phases

- **Phase 34**: Header File Processing (COMPLETE) - Multi-file infrastructure
- **Phase 48**: Namespaces - Often combined with modules
- **Phase 11**: Templates - Template modules

---

## Notes

- This is a **DEFERRED** phase - no implementation planned
- Detailed design deferred indefinitely
- Will be reconsidered only if triggers occur (high demand, widespread adoption)
- **VERY LOW priority** - focus on HIGH priority features first (Phases 47-49)
- **Architectural mismatch** - modules don't fit C compilation model
- **Zero semantic effect** - translation provides no behavioral benefit

---

**Last Updated**: 2025-12-27
**Status**: DEFERRED (VERY LOW Priority)
**Next Review**: 2026 (or when reconsideration triggers occur)
**Recommendation**: **REJECT** with clear error + migration guide (1-2 hours)
