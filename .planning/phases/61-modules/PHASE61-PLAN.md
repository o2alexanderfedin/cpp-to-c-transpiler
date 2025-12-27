# Phase 61: Modules (C++20)

**Status**: DEFERRED (VERY LOW Priority)
**Estimated Effort**: 150-200 hours
**Current Progress**: 0%
**Dependencies**: Build System Overhaul, Clang Module Support
**Target Completion**: Deferred until C++20 modules are widely adopted

## Objective

Implement support for C++20 Modules, enabling:
- Module declarations: `export module mymodule;`
- Module imports: `import mymodule;`
- Module partitions: `export module mymodule:partition;`
- Module interface units (.cppm, .ixx)
- Named modules replacing header files
- Improved build times and encapsulation

## Context: Why This Is Deferred

### Complexity Factors

1. **C++20 Feature - Extremely Limited Adoption**
   - C++20 modules are the newest major C++ feature (2020)
   - Compiler support is incomplete and evolving:
     - GCC: Partial support since GCC 11 (2021)
     - Clang: Partial support since Clang 15 (2022)
     - MSVC: Best support but still evolving
   - Build system support is nascent:
     - CMake: Experimental support since 3.20
     - Other build systems: Limited or no support
   - **Industry adoption: <1% of C++ codebases**

2. **Fundamental Build System Changes Required**
   - Modules require dependency scanning **before** compilation
   - Traditional compilation model (independent TUs) doesn't work
   - Build tools must understand module dependencies
   - Requires BMI (Binary Module Interface) generation/consumption
   - Our transpiler's build system would need complete overhaul

3. **Clang Frontend Dependency**
   - Clang's module support is still evolving
   - Module AST representation is complex
   - May require newer Clang versions than we currently support
   - Clang module compilation is significantly different from header compilation

4. **Translation Paradigm Mismatch**
   - Modules are designed to **replace** header files
   - C has no module system
   - Must translate back to header/source model
   - Loses many benefits of modules (build speed, encapsulation)

5. **Enormous Effort for Minimal Benefit**
   - 150-200 hours of implementation
   - <1% of C++ codebases use modules
   - Translation negates most module benefits
   - Can transpile 99.9%+ of C++ code without module support

### Strategic Decision

**DEFER INDEFINITELY** until:
- C++20 modules reach 25%+ adoption in industry
- Build system support is mature and standardized
- Clang module support is stable
- Clear user demand emerges
- Fundamental architecture decision: should transpiler support modules at all?

## Conceptual Translation Approach

Modules represent a **fundamental shift** in C++ compilation. Translation to C requires **flattening** back to header/source model.

### Example: Simple Module

**C++ Module Interface** (`math.cppm`):
```cpp
export module math;

export int add(int a, int b) {
    return a + b;
}

export int multiply(int a, int b) {
    return a * b;
}
```

**C++ Module User** (`main.cpp`):
```cpp
import math;

int main() {
    int x = add(5, 3);
    int y = multiply(4, 2);
    return 0;
}
```

**Transpiled C Header** (`math.h`):
```c
#ifndef MATH_H
#define MATH_H

int add(int a, int b);
int multiply(int a, int b);

#endif
```

**Transpiled C Implementation** (`math.c`):
```c
#include "math.h"

int add(int a, int b) {
    return a + b;
}

int multiply(int a, int b) {
    return a * b;
}
```

**Transpiled C Main** (`main.c`):
```c
#include "math.h"

int main() {
    int x = add(5, 3);
    int y = multiply(4, 2);
    return 0;
}
```

### Example: Module Partitions

**C++ Module Partition** (`math:impl.cppm`):
```cpp
module math:impl;  // Partition implementation

int add_impl(int a, int b) {
    return a + b;
}
```

**C++ Module Interface** (`math.cppm`):
```cpp
export module math;
import :impl;  // Import partition

export int add(int a, int b) {
    return add_impl(a, b);
}
```

**Transpiled C** (partitions flattened):
```c
// math_impl.h
int add_impl(int a, int b);

// math_impl.c
int add_impl(int a, int b) {
    return a + b;
}

// math.h
int add(int a, int b);

// math.c
#include "math_impl.h"

int add(int a, int b) {
    return add_impl(a, b);
}
```

### Example: Private Module Fragment

**C++**:
```cpp
export module utils;

export void public_api();

module :private;  // Private fragment - not exported

void internal_helper() {
    // Not visible to importers
}

void public_api() {
    internal_helper();
}
```

**Transpiled C**:
```c
// utils.h - only exported symbols
void public_api();

// utils.c - includes internal helpers
static void internal_helper() {
    // Internal linkage
}

void public_api() {
    internal_helper();
}
```

## Technical Challenges

### 1. Module Declaration Analysis

**Challenge**: Understand module structure from Clang AST

**C++ Module Syntax**:
```cpp
export module mymodule;           // Module declaration
export module mymodule:partition; // Partition declaration
module mymodule:partition;        // Partition implementation
module;                           // Global module fragment
module :private;                  // Private module fragment
```

**Required**:
- Detect module declarations in AST
- Identify module name and partition name
- Distinguish interface vs. implementation units
- Handle global/private module fragments

### 2. Module Import Resolution

**Challenge**: Resolve `import` statements to module contents

**C++ Imports**:
```cpp
import mymodule;              // Import entire module
import :partition;            // Import partition
import <iostream>;            // Import standard library module
import "myheader.h";          // Import header unit
```

**Required**:
- Build module dependency graph
- Locate module interface units
- Handle circular dependencies
- Map imports to C #includes

### 3. Export Analysis

**Challenge**: Determine what is exported from module

**C++ Export Syntax**:
```cpp
export int x;                     // Export variable
export void f();                  // Export function
export class C { };               // Export class
export { int a, b, c; }          // Export multiple
export namespace N { }            // Export namespace
export using ::global_func;       // Export using-declaration
```

**Required**:
- Track exported vs. non-exported declarations
- Handle export blocks
- Translate exported symbols to public API (header)
- Translate non-exported symbols to internal (static in .c)

### 4. Module Linkage Rules

**Challenge**: C++ modules have different linkage semantics

**Issues**:
- Non-exported entities have **module linkage** (not internal, not external)
- Different from C's static/extern model
- Template instantiations can cross module boundaries
- Inline functions have special rules

**Translation Strategy**:
- Module linkage → `static` in C (approximate)
- Exported → extern declarations in header
- Requires careful analysis of ODR implications

### 5. Build System Integration

**Challenge**: Modules require build order dependencies

**Problem**:
```
main.cpp imports math
  → Must compile math.cppm first to generate BMI
    → Must scan main.cpp to discover dependency
      → Chicken-and-egg problem
```

**C++ Build Flow with Modules**:
1. Scan all sources for `import` declarations
2. Build module dependency graph
3. Topologically sort modules
4. Compile modules in order, generating BMIs
5. Compile module users, consuming BMIs

**Our Transpiler**:
- Currently: Independent TU compilation
- With Modules: Must track dependencies, order compilation
- Build system overhaul required

### 6. Standard Library Modules

**Challenge**: C++20 defines standard library modules

**Standard Modules**:
```cpp
import std;           // All standard library
import std.core;      // Core language support
import std.io;        // I/O facilities
import std.regex;     // Regular expressions
```

**Problem**:
- Standard library modules not widely available yet
- Would need to map to C standard library
- Significant implementation effort

## Implementation Strategy (IF Pursued)

### Phase 61.1: Module Declaration Analysis (30-40 hrs)

**Objective**: Parse and understand module declarations

**Tasks**:
1. Detect module declarations in Clang AST
2. Extract module name, partition name
3. Identify module fragments (global, private)
4. Build module metadata structure

**Deliverables**:
- ModuleDeclaration AST analyzer
- ModuleRegistry to track modules
- Test suite for module parsing

**Clang AST Nodes**:
- `ModuleDecl` - module declaration
- `ImportDecl` - import declaration
- `ExportDecl` - export declaration

### Phase 61.2: Module Dependency Graph (40-50 hrs)

**Objective**: Build dependency graph of modules

**Tasks**:
1. Track all `import` declarations
2. Resolve imports to module definitions
3. Build directed acyclic graph (DAG)
4. Detect circular dependencies
5. Topologically sort modules

**Deliverables**:
- ModuleDependencyGraph class
- Import resolver
- Circular dependency detector
- Test suite for complex dependency scenarios

### Phase 61.3: Export Analysis (30-40 hrs)

**Objective**: Identify exported vs. non-exported declarations

**Tasks**:
1. Track all `export` declarations
2. Handle export blocks
3. Distinguish exported/non-exported symbols
4. Build public API surface

**Deliverables**:
- ExportAnalyzer class
- Exported symbol registry
- Test suite for export scenarios

### Phase 61.4: Module to Header/Source Translation (50-70 hrs)

**Objective**: Generate C header/source from modules

**Tasks**:
1. Generate header for exported symbols
2. Generate source with all definitions
3. Convert `import` to `#include`
4. Handle module linkage → static
5. Flatten module partitions

**Deliverables**:
- ModuleToHeaderTranslator class
- ModuleToSourceTranslator class
- Import to include mapper
- Test suite for translation

**Translation Rules**:
```
export module M;           → M.h header file
export int f();            → int f(); in M.h
int g();                   → static int g(); in M.c
import other;              → #include "other.h"
module :private;           → static symbols in M.c
```

## Dependencies

### Hard Dependencies

1. **Clang Module Support** (REQUIRED)
   - Clang must support modules (Clang 15+)
   - Module AST nodes available
   - BMI generation/consumption
   - Cannot implement without Clang support

2. **Build System Overhaul** (REQUIRED)
   - Dependency scanning infrastructure
   - Topological compilation ordering
   - Module dependency tracking
   - Completely new build pipeline

### Soft Dependencies

1. **Phase 11: Template Infrastructure**
   - Modules can export templates
   - Template instantiation across module boundaries

2. **Phase 1-10: Core Features**
   - Modules can export any C++ feature
   - Need robust translation for all features

## Success Criteria (IF Implemented)

### Functional Requirements

- [ ] **Module Declarations**
  - Parse `export module` declarations
  - Identify module interface vs. implementation units
  - Handle module partitions
  - Support global/private module fragments

- [ ] **Module Imports**
  - Resolve `import` statements
  - Build dependency graph
  - Detect circular dependencies
  - Translate to C #include

- [ ] **Export Analysis**
  - Identify exported declarations
  - Handle export blocks
  - Translate to public header API
  - Non-exported → static in .c

- [ ] **Module Translation**
  - Generate header for module interface
  - Generate source for module implementation
  - Flatten module partitions
  - Preserve encapsulation where possible

### Quality Requirements

- [ ] **Test Coverage**: 80%+ for module features
- [ ] **Build Integration**: Working build pipeline
- [ ] **Documentation**: Complete module translation guide
- [ ] **Performance**: Minimal overhead vs. header-based code

### Validation Cases

1. **Simple Module**
   ```cpp
   export module math;
   export int add(int a, int b);
   ```

2. **Module Partition**
   ```cpp
   export module utils:string;
   export module utils:io;
   export module utils;  // Re-export partitions
   ```

3. **Private Module Fragment**
   ```cpp
   export module api;
   export void public_func();
   module :private;
   void internal_func();  // Not exported
   ```

4. **Module Dependencies**
   ```cpp
   export module graphics;
   import math;  // Dependency
   export class Shape { };
   ```

5. **Header Unit Import**
   ```cpp
   export module wrapper;
   import <vector>;  // Import standard library header as module
   ```

## Risks and Mitigations

### Risk 1: Extremely Low Adoption

**Problem**: Modules may not be adopted for many years

**Mitigation**:
- Monitor adoption metrics annually
- Defer until 10%+ adoption
- Focus on features with immediate value

### Risk 2: Clang Module Support Instability

**Problem**: Clang's module implementation is still evolving

**Mitigation**:
- Target stable Clang version (e.g., Clang 18+)
- Test against multiple Clang versions
- Document supported Clang versions clearly

### Risk 3: Build System Complexity

**Problem**: Module-aware build system is extremely complex

**Mitigation**:
- Consider leveraging CMake's module support
- May require external build tool integration
- Start with simple module scenarios
- Document build requirements clearly

### Risk 4: Standard Library Modules

**Problem**: `import std;` is not widely available

**Mitigation**:
- Defer standard library module support
- Focus on user-defined modules only
- Provide migration path from headers

### Risk 5: Translation Loses Module Benefits

**Problem**: Translating modules back to headers negates benefits

**Mitigation**:
- Acknowledge this limitation upfront
- Modules are primarily for C++ build speed
- Transpilation target is C, not fast C++ builds
- Consider if module support is worth it at all

## Alternative Approach: Module Rejection

**Simplest Implementation**: Don't support modules at all

**Rationale**:
1. Modules are about **build performance** in C++
2. Transpilation target is C, which has headers
3. Translating modules → headers loses the point
4. <1% of C++ code uses modules
5. 150-200 hours of effort for minimal benefit

**User Guide**:
- "Convert your modules to header files before transpilation"
- Provide automated module → header conversion tool
- Document manual conversion process

**Pros**:
- Zero implementation effort
- Clear user expectation
- Focus on features that matter

**Cons**:
- Doesn't support cutting-edge C++20 code
- Users must refactor module-based code

**Recommendation**: This is the preferred approach unless strong user demand emerges.

## Recommendation

**DEFER INDEFINITELY** (or **DO NOT IMPLEMENT**)

**Rationale**:
1. **<1% adoption**: Modules are barely used in production C++ code
2. **Build system overhaul**: Requires fundamental changes to transpiler architecture
3. **Clang dependency**: Requires cutting-edge Clang support
4. **Lost in translation**: Module benefits (build speed) don't apply to C output
5. **Enormous effort**: 150-200 hours for feature almost nobody uses

**Alternative**:
- Provide module → header conversion tool (10-20 hours)
- Document manual conversion process
- Advise users to avoid modules in code intended for transpilation

**Reconsideration Triggers**:
- C++20 modules reach 25%+ industry adoption
- Multiple users specifically request module support
- Build system overhaul is undertaken for other reasons
- Industry consensus emerges that modules are "the future"

**Current Stance**: **Do not implement**. Guide users to refactor modules to headers.

## Resources

### Research Materials

- C++20 Modules specification (ISO/IEC 14882:2020 §10)
- Clang Modules documentation
- CMake module support documentation
- Build system integration patterns

### Related Phases

- **Phase 1-10**: All core features (modules can export anything)
- **Phase 11**: Templates (modules can export templates)
- **Build System**: Complete overhaul required

### Example Codebases

- Very few exist - modules are barely adopted
- Standard library implementations (experimental)
- Clang/GCC/MSVC test suites

### Compiler Support Status (as of 2025)

- **GCC 14**: Partial support, improving
- **Clang 18**: Partial support, improving
- **MSVC 2022**: Best support, but still incomplete
- **Build Systems**: CMake 3.28+ has experimental support

## Notes

- This is a **placeholder plan** for a feature that may **never be implemented**
- C++20 modules are too new and adoption is too low
- Translation to C negates most module benefits
- **VERY LOW PRIORITY** - recommend **not implementing** at all
- If users need modules, they should refactor to headers first

---

**Last Updated**: 2025-12-26
**Status**: DEFERRED (VERY LOW Priority / DO NOT IMPLEMENT)
**Next Review**: 2027 or when adoption reaches 10%
