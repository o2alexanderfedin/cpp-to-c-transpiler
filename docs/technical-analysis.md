# Clang-Based C++ to C Converter - Technical Feasibility Research

**Research Date:** December 7, 2025
**Version:** 1.0
**Status:** Comprehensive technical investigation completed

---

<research_output>

<executive_summary>

## Executive Summary

After comprehensive research into the technical feasibility of building a Clang-based tool that converts modern C++ code (C++11/14/17/20/23) to human-readable, compilable C code with `#line` directives, the assessment is: **PARTIALLY VIABLE with significant constraints**.

**Recommended Interception Point:** AST-level interception using Clang's RecursiveASTVisitor after semantic analysis (Sema) but before CodeGen. This preserves high-level C++ semantics while providing access to fully-typed, semantically-analyzed constructs. Intercepting at LLVM IR level (like llvm-cbe) produces unreadable output due to loss of high-level abstractions.

**Major Technical Challenges:**
1. **Template Monomorphization** - Requires extracting all template instantiations from Clang's AST and generating separate C functions for each, leading to significant code explosion for heavily templated code
2. **Exception Handling** - No elegant C equivalent exists; setjmp/longjmp implementation is complex, has performance overhead, and doesn't support RAII cleanup
3. **RAII (Destructor Injection)** - Requires sophisticated control-flow analysis to inject destructor calls at all exit points (return, goto, exception, fall-through)
4. **STL Dependencies** - Either requires reimplementing STL containers/algorithms in C (massive undertaking) or linking against C++ runtime (defeats the purpose)

**Overall Assessment: PARTIALLY VIABLE**

A Clang-based C++ to C converter is technically feasible for a **pragmatic subset** of C++, but attempting to support ALL contemporary C++ features (especially exceptions, full RAII with complex control flow, and extensive STL usage) would result in either unreadable C code or an engineering effort comparable to building a C++ compiler from scratch. The most realistic approach is targeting a defined subset of C++ features that map cleanly to C idioms, similar to the strategy used by emmtrix eCPP2C (the only production-grade commercial tool).

**Key Insight:** The fundamental tension is between **completeness** (supporting all C++ features) and **readability** (generating maintainable C code). These goals are inherently conflicting - attempting both simultaneously will fail. Success requires explicitly choosing a middle ground: support common C++ patterns well, provide readable output for those patterns, and clearly document unsupported features.

</executive_summary>

<clang_architecture>

<compilation_pipeline>

## Clang Compilation Pipeline Architecture

Clang's compilation process follows a traditional multi-stage architecture:

### Pipeline Stages

```
Source Code (.cpp)
    ↓
[1] Lexer (Tokenization)
    ↓
[2] Parser (Syntax Analysis)
    ↓
[3] AST Construction
    ↓
[4] Sema (Semantic Analysis)
    ↓  ← ★ RECOMMENDED INTERCEPTION POINT
[5] CodeGen (LLVM IR Generation)
    ↓
[6] LLVM Optimization Pipeline
    ↓
[7] Machine Code Generation
    ↓
Binary Output
```

**Key Characteristics:**
- **Lexer**: Converts source text into tokens (keywords, identifiers, operators, literals)
- **Parser**: Builds Abstract Syntax Tree (AST) from tokens following C++ grammar rules
- **AST**: Tree representation preserving source structure (statements, expressions, declarations)
- **Sema**: Type checking, name resolution, template instantiation, overload resolution
- **CodeGen**: Converts typed AST to LLVM Intermediate Representation (IR), losing high-level abstractions

### Critical AST Properties

After Sema phase, the AST contains:
- **Fully-resolved types** (auto deduced, template parameters substituted)
- **Instantiated templates** (all used template specializations available as ClassTemplateSpecializationDecl nodes)
- **Resolved overloads** (which operator/function was selected)
- **Implicit conversions** (constructor calls, type casts inserted)
- **Source location information** (file, line, column for every AST node via SourceLocation)
- **Semantic annotations** (const, constexpr evaluation results, lifetime information)

**Why AST is superior to LLVM IR for readable C generation:**
- Preserves class/struct boundaries (IR flattens to registers and memory operations)
- Maintains function signatures and parameter names (IR uses numbered registers)
- Keeps loop structure intact (IR uses basic blocks and branches)
- Retains type information (IR has minimal types: i32, i64, ptr, etc.)

</compilation_pipeline>

<recommended_approach>

## Recommended Approach: AST-Based Transformation

### Architecture: LibTooling Standalone Tool

**Chosen Architecture:** Standalone executable using Clang's LibTooling infrastructure

**Justification:**
- **Plugin vs Standalone**: Plugins integrate into Clang compilation, but our goal is source-to-source transformation, not analysis during normal compilation. Standalone tool provides full control over input/output, doesn't require modifying user's compiler setup
- **LibTooling advantages**: Handles compilation database (`compile_commands.json`), manages include paths, preprocessor state, provides ClangTool abstraction for processing multiple files

### Core Implementation Components

```cpp
// High-level architecture (pseudocode)

class Cpp2CASTConsumer : public clang::ASTConsumer {
  void HandleTranslationUnit(clang::ASTContext &Context) override {
    // Entry point: process entire translation unit
    CppToCVisitor Visitor(Context, OutputEmitter);
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());
  }
};

class CppToCVisitor : public clang::RecursiveASTVisitor<CppToCVisitor> {
public:
  // Declaration visitors
  bool VisitCXXRecordDecl(clang::CXXRecordDecl *D);  // Classes/structs
  bool VisitFunctionDecl(clang::FunctionDecl *D);    // Functions
  bool VisitVarDecl(clang::VarDecl *D);              // Variables
  bool VisitClassTemplateSpecializationDecl(clang::ClassTemplateSpecializationDecl *D);

  // Statement visitors
  bool VisitCXXConstructExpr(clang::CXXConstructExpr *E);  // Constructor calls
  bool VisitCXXMemberCallExpr(clang::CXXMemberCallExpr *E); // Member function calls
  bool VisitCXXForRangeStmt(clang::CXXForRangeStmt *S);     // Range-based for
  bool VisitLambdaExpr(clang::LambdaExpr *E);               // Lambda expressions

  // Type visitors
  bool VisitQualType(clang::QualType T);
};

class CCodeEmitter {
  // Generates C code with proper formatting
  void emitStruct(const ClassInfo &Info);
  void emitFunction(const FunctionInfo &Info);
  void emitLineDirective(clang::SourceLocation Loc);
  void emitVtable(const ClassInfo &Info);
};
```

### Key Clang APIs to Utilize

**AST Traversal:**
- `RecursiveASTVisitor<Derived>` - Template base class providing visitor pattern for all AST node types
- `ASTConsumer` - Interface for receiving full translation unit AST
- `ASTFrontendAction` - Entry point for LibTooling-based tools

**AST Interrogation:**
- `CXXRecordDecl` - Class/struct declarations, provides methods, base classes, virtual function info
- `ClassTemplateSpecializationDecl` - Template instantiations with concrete type arguments
- `FunctionDecl`, `CXXMethodDecl`, `CXXConstructorDecl`, `CXXDestructorDecl` - Function-related nodes
- `Stmt` hierarchy - Statements (if, for, while, return, etc.)
- `Expr` hierarchy - Expressions (calls, operators, literals, casts)
- `QualType` - Qualified types (const int*, volatile MyClass&, etc.)

**Source Manipulation:**
- `SourceLocation` - Represents a location in source code (file + offset)
- `SourceRange` - Span of source code (begin + end SourceLocation)
- `SourceManager` - Maps SourceLocations to file/line/column, handles `#include` expansion
- `PresumedLoc` - Respects `#line` directives for diagnostic output (model for our own generation)
- `Rewriter` - API for modifying source code (not suitable for our use case - we're generating new C, not modifying C++)

**Pretty Printing:**
- `StmtPrinter`, `DeclPrinter` - Clang's own AST-to-source code printers (can be studied for patterns, but print C++ not C)
- `PrintingPolicy` - Controls how AST nodes are converted to text (booleans, namespaces, etc.)

</recommended_approach>

<implementation_strategy>

## Implementation Strategy: Plugin vs Standalone Tool

### Decision: Standalone LibTooling-based Tool

**Rationale:**

**Clang Plugin Characteristics:**
- Integrated into Clang compilation process
- Loaded dynamically with `-fplugin=`
- Runs during compilation alongside normal CodeGen
- Best for: Static analysis, diagnostics, minor transformations during build

**Standalone Tool Characteristics:**
- Separate executable invoking Clang as library
- Full control over input/output
- Can process multiple files via compilation database
- Best for: Source-to-source transformations, major code generation

**Why Standalone for C++ to C:**
1. **Output control**: Need to generate entirely new `.c` and `.h` files, not modify existing sources
2. **Multi-pass processing**: May need multiple passes (dependency analysis, then emission)
3. **Build system integration**: Acts as separate build step (like protobuf compiler)
4. **User experience**: Simple CLI tool: `cpp2c input.cpp -o output.c`

### Build System Integration

**Compilation Database Support:**
```bash
# Project uses CMake
cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON .

# Generates compile_commands.json with:
# - Compiler flags (-std=c++17, -I/usr/include/mylib, -DNDEBUG)
# - Source file paths
# - Working directories

# Tool reads database to get accurate compiler settings
cpp2c --compile-commands=compile_commands.json src/myfile.cpp
```

**Alternative for Non-CMake Projects:**
- Use `bear` tool to intercept compiler invocations and generate database
- Manual specification of include paths and flags: `cpp2c -I/usr/include --std=c++17 myfile.cpp`

### LibTooling Infrastructure

**Core Classes:**
```cpp
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"

int main(int argc, const char **argv) {
  auto ExpectedParser = CommonOptionsParser::create(argc, argv, MyToolCategory);
  CommonOptionsParser &OptionsParser = ExpectedParser.get();

  ClangTool Tool(OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());

  return Tool.run(newFrontendActionFactory<Cpp2CAction>().get());
}
```

**Advantages:**
- `CommonOptionsParser` handles command-line parsing (`--help`, `--`, compilation database)
- `ClangTool` manages running FrontendActions over multiple files
- Automatically handles include resolution, preprocessor directives, macro expansion

</implementation_strategy>

</clang_architecture>

<existing_tools>

<tool name="emmtrix eCPP2C">
<url>https://www.emmtrix.com/tools/emmtrix-cpp-to-c-compiler</url>

<architecture>

### Technical Architecture (Based on Available Documentation)

**Foundation:** LLVM/Clang-based compiler technology

**Design Philosophy:** Binary equivalence - the compiled LLVM IR of the original C++ code and translated C code should be nearly identical

**Implementation Strategy (Inferred):**
1. Parse C++ with Clang to AST
2. Perform semantic analysis (type resolution, template instantiation)
3. Transform AST to C-compatible representation
4. Generate C code designed to produce similar LLVM IR when compiled
5. Validate correctness via IR comparison using `llvm-diff`

**Key Insight from Testing Methodology:**
- They compile both C++ and generated C to LLVM IR
- Apply optimizations to both
- Use `llvm-diff` to verify equivalence
- This suggests code generation targets LLVM IR semantics, not human readability

**Supported Features:**
- C++17 standard (ISO/IEC 14882:2017)
- GCC/Clang language extensions (GNU attributes, inline assembly, etc.)
- Full template support (likely via monomorphization)
- Full STL support (likely requires C++ standard library linking or C reimplementation)

</architecture>

<lessons_learned>

### Critical Lessons from emmtrix eCPP2C

**1. Binary Equivalence as Correctness Criterion**
- Rather than trying to preserve C++ semantics at source level, target LLVM IR equivalence
- This allows aggressive transformations that might look "weird" in C but compile to same machine code
- Validation is automated: compile both to IR, compare with `llvm-diff`

**2. Commercial Viability Requires Narrow Focus**
- emmtrix targets safety-critical embedded systems (ISO 26262, DO-178C)
- Use case: Run C++ through C-focused static analyzers (MISRA C, Polyspace, TÜV-certified tools)
- Not attempting to make generated C human-maintainable
- This narrow focus makes product viable where general-purpose solution would fail

**3. Likely Complexity (Estimated)**
- Commercial product with qualification kits, ongoing support since ~2020
- Likely represents multiple person-years of engineering effort
- Supports C++17 fully - indicates mature, comprehensive implementation
- Online compiler explorer suggests sophisticated infrastructure

**4. Output Quality Unknown**
- No public examples of generated C code available
- Likely machine-generated (based on IR-equivalence goal)
- Probably not suitable for manual modification
- Focus on "analyzable" C, not "readable" C

</lessons_learned>

<reusable_patterns>

### Patterns Applicable to Open-Source Implementation

**1. Testing Strategy:**
```python
def validate_conversion(cpp_file, c_file):
    # Compile C++ to LLVM IR
    run(["clang++", "-S", "-emit-llvm", "-O2", cpp_file, "-o", "original.ll"])

    # Compile generated C to LLVM IR
    run(["clang", "-S", "-emit-llvm", "-O2", c_file, "-o", "generated.ll"])

    # Compare IRs (allowing for minor differences)
    run(["llvm-diff", "original.ll", "generated.ll"])
```

**2. Leverage Clang for Heavy Lifting:**
- Let Clang handle template instantiation (don't reimplement C++ semantics)
- Extract instantiated templates from AST (ClassTemplateSpecializationDecl)
- Generate one C function per template instantiation

**3. Accept C++ Runtime Dependency (Pragmatic Approach):**
- emmtrix likely links against C++ standard library
- Attempting to reimplement STL in C is impractical
- Alternative: Generate C code that links with `libstdc++` or `libc++`
- Downside: Not "pure C", but pragmatic for real-world usage

**4. Focus on Specific Use Case:**
- Don't try to be general-purpose
- Define target subset of C++ (e.g., "C++ without exceptions", "C++17 minus concepts")
- Document unsupported features clearly
- Fail gracefully with clear error messages for unsupported constructs

</reusable_patterns>

</tool>

<tool name="llvm-cbe">
<url>https://github.com/JuliaHubOSS/llvm-cbe</url>

<architecture>

### Technical Architecture

**Pipeline:** LLVM IR → C Code

**Position in Compilation Flow:**
```
C++ Source → Clang → LLVM IR → llvm-cbe → C Code
                      ↑
                      └─ Interception point (too late for readable output)
```

**Why It Exists:**
- Julia language ecosystem needed C backend for certain platforms
- LLVM removed official C backend in 2014 (couldn't handle modern IR features)
- Community resurrection by JuliaComputing maintains compatibility with LLVM 20

**Technical Implementation:**
- Operates on LLVM IR (low-level, SSA form, architecture-neutral)
- Converts IR instructions to C equivalents:
  - `%1 = add i32 %0, 1` → `_1 = _0 + 1;`
  - `br label %loop` → `goto loop;`
  - `call @foo()` → `foo();`
- Handles phi nodes (SSA merges) with explicit C variables
- Generates struct layouts for LLVM aggregate types

**Output Characteristics:**
```c
// Typical llvm-cbe output (simplified example)
struct l_struct_OC_MyClass {
  unsigned int field_vtable_ptr;
  unsigned int field_member_x;
  unsigned long long field_member_y;
};

unsigned long long _ZN7MyClass10myFunctionEv(struct l_struct_OC_MyClass* _this) {
  unsigned int _1;
  unsigned int _2;
  unsigned long long _3;
  // SSA-style numbered variables
  _1 = *((&(((&_this->field_vtable_ptr)))));
  _2 = *((&(((&_this->field_member_x)))));
  _3 = (((unsigned long long)(llvm_add_u32(_1, _2))));
  return _3;
}
```

**Key Problems:**
1. **Mangled names preserved**: `_ZN7MyClass10myFunctionEv` instead of `MyClass_myFunction`
2. **Numbered variables**: SSA form leaks through (`_1`, `_2`, `_3`)
3. **Excessive pointer dereferencing**: `*((&(((&_this->field_member_x)))))`
4. **Loss of control flow**: Goto-based (basic blocks), not structured if/while/for
5. **No type abstraction**: Everything becomes primitive types and pointers

</architecture>

<lessons_learned>

### Critical Lessons from llvm-cbe Failure Mode

**1. LLVM IR Is Too Low-Level for Readable C**
- IR is designed for optimization, not source-level semantics
- Loop structures become basic blocks + branches + phi nodes
- High-level types flattened to bytes and pointers
- Conclusion: **Must intercept at AST level, not IR level**

**2. Why Official C Backend Was Removed**
- Couldn't handle modern LLVM IR features (vector instructions, atomic operations, invoke/landingpad for exceptions)
- Generated code was unreadable and unmaintainable
- LLVM community decided backends should target machine code, not source languages
- Community resurrection (llvm-cbe) only succeeds for Julia's specific use case (where readability isn't required)

**3. What NOT to Do:**
- Don't work from LLVM IR if goal is readable C
- Don't preserve mangled names (demangle or use original C++ names)
- Don't use SSA-style numbered variables (recover original variable names from AST)
- Don't generate goto-based code (preserve structured control flow from AST)

**4. What It Does Right (Technically):**
- Generates compilable, functionally correct C code
- Handles complex LLVM constructs (phi nodes, exception tables, etc.)
- Demonstrates that C can represent any computation (Church-Turing)
- But proves that "compilable" ≠ "maintainable"

</lessons_learned>

<reusable_patterns>

### Applicable Techniques (What to Salvage)

**1. Struct Layout for Classes:**
```c
// llvm-cbe approach (adapted for readability)
struct MyClass {
    void** vtable;  // Virtual function table pointer
    int member_x;
    long long member_y;
};
```
- Classes → structs with vtable pointer as first member
- Maintain ABI compatibility for memory layout

**2. Name Demangling Strategy:**
- llvm-cbe fails by keeping mangled names
- Better approach: Use Clang's AST to get original C++ names
- Apply readable name transformation: `MyClass::myFunction()` → `MyClass_myFunction()`

**3. Avoiding llvm-cbe's Mistakes:**
- Preserve AST-level variable names (use Clang's NamedDecl)
- Maintain structured control flow (if/while/for from CXX*Stmt nodes)
- Don't introduce temporary numbered variables unless necessary
- Keep type abstractions via typedefs

</reusable_patterns>

</tool>

<tool name="Clava">
<url>https://github.com/specs-feup/clava</url>

<architecture>

### Technical Architecture

**Type:** Source-to-source compiler (C/C++ → C/C++, same language transformations)

**Core Technology:**
- Built on Clang for C++ parsing
- Uses LARA (Language-Agnostic Specification Language) for transformations
- LARA is JavaScript/TypeScript-based DSL for code manipulation
- Distributed as NPM package (Node.js + Java runtime)

**Design Philosophy:**
- Aspect-oriented programming for code transformations
- Composable, reusable transformation scripts
- Focus on HPC optimizations, parallelization, hardware/software partitioning

**Architecture Layers:**
```
C++ Source Code
    ↓
Clang Parser → AST
    ↓
ClavaWeaver (AST → LARA Objects)
    ↓
LARA Scripts (User transformations)
    ↓
Modified AST
    ↓
Code Generation → C++ Source
```

**Example LARA Script (Simplified):**
```javascript
// Find all for loops and annotate for OpenMP parallelization
aspectdef ParallelizeLoops
    select loop.for end
    apply
        $for.insert_before("#pragma omp parallel for");
    end
end
```

**Key Capabilities:**
- Function outlining (extract function from code region)
- Voidification (convert non-void functions to void with out-parameters)
- Array/struct flattening
- Constant folding and propagation
- Loop transformations (unrolling, tiling, interchange)
- Integration with Vitis HLS for FPGA synthesis

</architecture>

<lessons_learned>

### Lessons from Clava's Source-to-Source Approach

**1. Separation of Concerns Works**
- Clang handles parsing (don't reimplement C++ grammar)
- LARA handles transformations (domain-specific logic)
- Code generation reuses Clang's pretty-printer where possible
- **Applicable to C++ → C:** Leverage Clang's AST, focus on C code emission

**2. AST Manipulation Patterns**
- Visit nodes with RecursiveASTVisitor
- Build internal representation (Clava's "weaver" model)
- Apply transformations
- Regenerate source code
- **For C++ → C:** Similar pattern, but internal representation is "C equivalent" not "modified C++"

**3. Challenges They Faced:**
- Preserving source formatting (whitespace, comments)
- Handling macros and preprocessor directives
- Maintaining source location information for error messages
- **Relevant to us:** Same challenges exist for C generation, must emit `#line` directives

**4. Not Applicable to C++ → C (But Still Valuable):**
- Clava transforms C++ to optimized C++, not different language
- However, architecture demonstrates successful AST-based transformation tool
- Active maintenance, academic backing, published research
- Proves AST-based approach is viable for production tools

</lessons_learned>

<reusable_patterns>

### Architectural Patterns to Adopt

**1. Multi-Pass Processing:**
```python
# Clava pattern (adapted)
class ConversionPipeline:
    def pass1_dependency_analysis(self, ast):
        # Identify all types, forward declarations needed
        pass

    def pass2_type_generation(self, ast):
        # Generate C structs, typedefs, enums
        pass

    def pass3_function_generation(self, ast):
        # Generate C functions with proper signatures
        pass

    def pass4_implementation(self, ast):
        # Generate function bodies
        pass
```

**2. Preserving Source Context:**
- Clava maintains source locations throughout transformations
- Generates code with correct line numbers for debugging
- **For C++ → C:** Essential for `#line` directives mapping back to original C++ source

**3. Testing Infrastructure:**
- Clava has extensive test suite
- Integration with CSmith for fuzz testing
- **For C++ → C:** Need comprehensive test suite covering C++ feature matrix

**4. Extensible Architecture:**
- LARA scripts allow user customization
- **For C++ → C:** Consider plugin system for custom C code generation strategies

</reusable_patterns>

</tool>

</existing_tools>

<feature_conversion_matrix>

## C++ Feature Conversion Strategies

<feature name="Classes and Objects">

<c_representation>

### C Representation Strategy

**Basic Class → Struct Conversion:**

```cpp
// C++ Input
class MyClass {
private:
    int x;
    double y;
public:
    MyClass(int x, double y);
    ~MyClass();
    void method();
    int getX() const;
};
```

```c
// Generated C Output
typedef struct MyClass {
    int x;
    double y;
} MyClass;

// Constructor → init function
void MyClass_init(MyClass* this, int x, double y) {
    this->x = x;
    this->y = y;
}

// Destructor → cleanup function
void MyClass_destroy(MyClass* this) {
    // Cleanup logic
}

// Member function → static function with this pointer
void MyClass_method(MyClass* this) {
    // Implementation
}

// Const method → const pointer parameter
int MyClass_getX(const MyClass* this) {
    return this->x;
}
```

**Virtual Functions → VTable Implementation:**

```cpp
// C++ Input
class Base {
public:
    virtual ~Base();
    virtual void foo();
    virtual int bar(int x);
};

class Derived : public Base {
public:
    void foo() override;
    int bar(int x) override;
};
```

```c
// Generated C Output

// Forward declarations
typedef struct Base Base;
typedef struct Derived Derived;

// VTable structures
typedef struct Base_vtable {
    void (*destructor)(Base* this);
    void (*foo)(Base* this);
    int (*bar)(Base* this, int x);
} Base_vtable;

typedef struct Derived_vtable {
    void (*destructor)(Derived* this);
    void (*foo)(Derived* this);
    int (*bar)(Derived* this, int x);
} Derived_vtable;

// Class structures (vtable pointer as first member)
struct Base {
    const Base_vtable* vtable;
    // Base data members
};

struct Derived {
    Base base;  // Inherit via composition
    // Derived data members
};

// Virtual function implementations
void Base_destructor_impl(Base* this) { /* ... */ }
void Base_foo_impl(Base* this) { /* ... */ }
int Base_bar_impl(Base* this, int x) { /* ... */ }

void Derived_destructor_impl(Derived* this) { /* ... */ }
void Derived_foo_impl(Derived* this) { /* ... */ }
int Derived_bar_impl(Derived* this, int x) { /* ... */ }

// VTable instances (const, read-only memory)
static const Base_vtable Base_vtable_instance = {
    .destructor = Base_destructor_impl,
    .foo = Base_foo_impl,
    .bar = Base_bar_impl
};

static const Derived_vtable Derived_vtable_instance = {
    .destructor = (void(*)(Base*))Derived_destructor_impl,
    .foo = (void(*)(Base*))Derived_foo_impl,
    .bar = (int(*)(Base*, int))Derived_bar_impl
};

// Constructors initialize vtable pointer
void Base_init(Base* this) {
    this->vtable = &Base_vtable_instance;
}

void Derived_init(Derived* this) {
    ((Base*)this)->vtable = (const Base_vtable*)&Derived_vtable_instance;
}

// Virtual dispatch
void call_foo(Base* obj) {
    obj->vtable->foo(obj);  // Dynamic dispatch
}
```

</c_representation>

<complexity>Medium</complexity>

<feasibility>Straightforward with caveats</feasibility>

<implementation_notes>

**Straightforward Aspects:**
- Simple classes → structs (trivial transformation)
- Member functions → static functions with `this` pointer (well-understood pattern)
- Single inheritance → struct embedding (first member is base struct)
- Access control (private/protected/public) → naming conventions or header separation

**Challenging Aspects:**
- **Virtual functions**: Requires generating vtable structs, vtable instances, and dispatch code
- **Multiple inheritance**: Requires offset adjustments for `this` pointer, multiple vtable pointers
- **Virtual inheritance** (diamond problem): Complex vtable layout with virtual base table offsets
- **Covariant return types**: Requires careful casting in generated C
- **Member function pointers**: Complex representation (offset + vtable index)

**Clang APIs to Use:**
- `CXXRecordDecl::bases()` - Get base classes
- `CXXRecordDecl::methods()` - Get all member functions
- `CXXMethodDecl::isVirtual()` - Check if method is virtual
- `CXXRecordDecl::getDestructor()` - Get destructor declaration
- `ASTContext::getASTRecordLayout()` - Get memory layout (field offsets, alignment)

**Gotchas:**
- Constructor/destructor call chains in inheritance hierarchies
- Virtual base class initialization (called only once in diamond inheritance)
- Access to protected members from derived classes
- Friend classes/functions (no C equivalent, may need to expose internals)

</implementation_notes>

</feature>

<feature name="Templates">

<c_representation>

### C Representation: Monomorphization

**Strategy:** Extract all template instantiations used in the program and generate separate C functions/structs for each.

```cpp
// C++ Input
template<typename T>
T max(T a, T b) {
    return a > b ? a : b;
}

template<typename T>
class Vector {
    T* data;
    size_t size;
public:
    void push_back(const T& value);
    T& operator[](size_t index);
};

// Usage
int main() {
    int x = max<int>(5, 10);
    double y = max<double>(3.14, 2.71);

    Vector<int> v1;
    Vector<std::string> v2;
}
```

```c
// Generated C Output (monomorphized)

// max<int> instantiation
int max_int(int a, int b) {
    return a > b ? a : b;
}

// max<double> instantiation
double max_double(double a, double b) {
    return a > b ? a : b;
}

// Vector<int> instantiation
typedef struct Vector_int {
    int* data;
    size_t size;
} Vector_int;

void Vector_int_push_back(Vector_int* this, const int* value);
int* Vector_int_subscript(Vector_int* this, size_t index);

// Vector<string> instantiation (requires std::string → C string handling)
typedef struct Vector_string {
    String* data;  // Assuming String is C representation of std::string
    size_t size;
} Vector_string;

void Vector_string_push_back(Vector_string* this, const String* value);
String* Vector_string_subscript(Vector_string* this, size_t index);

int main(void) {
    int x = max_int(5, 10);
    double y = max_double(3.14, 2.71);

    Vector_int v1;
    Vector_string v2;
    return 0;
}
```

</c_representation>

<complexity>High</complexity>

<feasibility>Challenging but viable for common cases</feasibility>

<implementation_notes>

**How It Works:**
1. Clang performs template instantiation during semantic analysis
2. All used instantiations appear in AST as `ClassTemplateSpecializationDecl` or `FunctionDecl` nodes
3. Traverse AST collecting all instantiated templates
4. Generate C code for each instantiation with mangled names

**Clang APIs:**
- `ClassTemplateDecl::specializations()` - Get all specializations of class template
- `ClassTemplateSpecializationDecl::getTemplateArgs()` - Get concrete type arguments
- `FunctionDecl::getTemplateSpecializationKind()` - Check if function is template instantiation
- `FunctionDecl::getTemplateInstantiationArgs()` - Get template arguments

**Challenges:**

**1. Name Mangling for Generated Functions:**
```cpp
// C++ can overload, C cannot
template<typename T> void foo(T x);
foo<int>(5);     // Becomes: foo_int(5)
foo<double>(3.14); // Becomes: foo_double(3.14)
```

**2. Non-Type Template Parameters:**
```cpp
template<int N>
struct Array {
    int data[N];
};

Array<10> arr1;  // Becomes: struct Array_10 { int data[10]; };
Array<20> arr2;  // Becomes: struct Array_20 { int data[20]; };
```

**3. Dependent Types:**
```cpp
template<typename T>
void process(typename T::value_type x) {  // value_type depends on T
    // ...
}
```
- After instantiation, `typename T::value_type` is resolved to concrete type
- Extract resolved type from AST, not original template

**4. Template Metaprogramming (SFINAE, enable_if):**
```cpp
template<typename T>
typename std::enable_if<std::is_integral<T>::value, T>::type
process(T x) { return x * 2; }
```
- Clang resolves which template specializations are viable
- Only emit C code for selected specializations
- SFINAE failures don't appear in AST

**5. Code Explosion:**
- Heavily templated code generates many instantiations
- `std::vector<int>`, `std::vector<double>`, `std::vector<MyClass>` → 3 separate C structs
- Can lead to very large C output files
- Mitigation: Detect identical instantiations, generate generic void* versions

**Partial Specialization:**
```cpp
template<typename T> struct Traits;         // Primary template
template<> struct Traits<int> { /*...*/ };  // Full specialization
template<typename T> struct Traits<T*> { /*...*/ }; // Partial specialization
```
- Clang selects correct specialization based on usage
- Emit C code only for selected specialization

**What's NOT Possible:**
- Generic templates (C has no generics, only via macros which are not type-safe)
- Template template parameters (no C equivalent)
- Variadic templates → requires generating overloads for each arity

**Success Criteria:**
- Can handle common STL containers (vector, map, string) via monomorphization
- Generates readable names: `Vector_int`, not `_Z6VectorIiE`
- Warns about excessive code bloat (e.g., >100 instantiations)

</implementation_notes>

</feature>

<feature name="RAII (Resource Acquisition Is Initialization)">

<c_representation>

### C Representation: Explicit Cleanup with Injected Calls

**C++ RAII Pattern:**
```cpp
void processFile(const char* filename) {
    std::ifstream file(filename);  // Constructor acquires resource

    if (!file.is_open()) {
        throw std::runtime_error("Cannot open file");
    }

    std::string line;
    while (std::getline(file, line)) {
        process(line);
    }

    // Destructor automatically called here, closes file
    // Even if exception thrown, destructor runs (stack unwinding)
}
```

**C Equivalent (Requires Explicit Cleanup):**
```c
void processFile(const char* filename) {
    FILE* file = NULL;
    char* line = NULL;
    size_t len = 0;
    int error = 0;

    file = fopen(filename, "r");
    if (file == NULL) {
        // Error handling, no cleanup needed yet
        return;
    }

    while (getline(&line, &len, file) != -1) {
        error = process(line);
        if (error != 0) {
            goto cleanup;  // Jump to cleanup on error
        }
    }

cleanup:
    if (line != NULL) {
        free(line);
    }
    if (file != NULL) {
        fclose(file);
    }

    if (error != 0) {
        // Propagate error via return code
    }
}
```

**Automated RAII → Cleanup Injection:**

The converter must identify all scope exit points and inject destructor calls:

```cpp
// C++ Input
void complexFunction() {
    MyResource r1;  // Constructor

    if (condition1) {
        MyResource r2;  // Constructor
        doWork();
        if (condition2) {
            return;  // ← Destructor for r2, then r1
        }
        moreWork();
        // ← Destructor for r2
    }

    if (condition3) {
        throw MyException();  // ← Destructor for r1 during unwinding
    }

    // ← Destructor for r1
}
```

```c
// Generated C with cleanup injection
void complexFunction(void) {
    MyResource r1;
    MyResource_init(&r1);

    if (condition1) {
        MyResource r2;
        MyResource_init(&r2);

        doWork();

        if (condition2) {
            MyResource_destroy(&r2);  // ← Injected cleanup
            MyResource_destroy(&r1);  // ← Injected cleanup
            return;
        }

        moreWork();

        MyResource_destroy(&r2);  // ← Injected cleanup
    }

    if (condition3) {
        MyResource_destroy(&r1);  // ← Injected cleanup
        // Exception handling (see exceptions feature)
        return;
    }

    MyResource_destroy(&r1);  // ← Injected cleanup
}
```

</c_representation>

<complexity>High</complexity>

<feasibility>Challenging - requires control-flow analysis</feasibility>

<implementation_notes>

**Core Challenge:** Identifying ALL scope exit points

**Exit Points to Handle:**
1. End of scope (closing `}`)
2. `return` statements
3. `break` statements (exit loop, but not function)
4. `continue` statements (end loop iteration, but not loop)
5. `goto` statements
6. Exception throws (see exceptions feature)

**Control Flow Analysis Required:**

**Algorithm:**
```python
def inject_destructors(function_body):
    # Build control flow graph (CFG)
    cfg = build_cfg(function_body)

    # For each block in CFG:
    for block in cfg.blocks:
        # Track live objects (constructed but not yet destroyed)
        live_objects = get_live_objects(block)

        # For each exit edge:
        for exit_edge in block.exits:
            # Inject destructor calls in reverse construction order
            for obj in reversed(live_objects):
                inject_call(exit_edge, f"{obj.type}_destroy(&{obj.name})")
```

**Clang APIs:**
- `CFG::buildCFG()` - Build control flow graph for function
- `CFG::getEntry()`, `CFG::getExit()` - Get entry/exit blocks
- `CFGBlock::succ_begin()`, `CFGBlock::succ_end()` - Get successor blocks
- `VarDecl::hasLocalStorage()` - Check if variable needs destruction

**Example: Complex Control Flow**

```cpp
void example() {
    Resource r1;

    for (int i = 0; i < 10; i++) {
        Resource r2;

        if (i == 5) {
            break;      // ← Destroy r2, then exit loop (r1 still alive)
        }

        if (i == 7) {
            continue;   // ← Destroy r2, then next iteration (r1 still alive)
        }

        // ← Destroy r2 at end of loop iteration
    }

    // ← Destroy r1 at end of function
}
```

**Generated C:**
```c
void example(void) {
    Resource r1;
    Resource_init(&r1);

    for (int i = 0; i < 10; i++) {
        Resource r2;
        Resource_init(&r2);

        if (i == 5) {
            Resource_destroy(&r2);  // ← Cleanup before break
            break;
        }

        if (i == 7) {
            Resource_destroy(&r2);  // ← Cleanup before continue
            continue;
        }

        Resource_destroy(&r2);  // ← Cleanup at scope exit
    }

    Resource_destroy(&r1);  // ← Final cleanup
}
```

**Interaction with Exceptions:**

If exceptions are supported (via setjmp/longjmp), RAII becomes even more complex:

```c
// RAII + exceptions requires setjmp at every scope with destructible objects
void example_with_exceptions(void) {
    jmp_buf cleanup_r1;
    Resource r1;
    Resource_init(&r1);

    if (setjmp(cleanup_r1) != 0) {
        // Exception caught, cleanup r1
        Resource_destroy(&r1);
        rethrow();  // Propagate to caller
    }

    // Function body...
    doWork();  // Might throw

    // Normal cleanup
    Resource_destroy(&r1);
}
```

**Optimization Opportunities:**
- If destructor is trivial (does nothing), omit calls
- Reorder cleanup code to minimize duplicated destructor calls
- Use goto for cleanup (C idiom: single cleanup label at function end)

**Limitations:**
- Cannot handle placement new/delete (explicit memory management)
- Difficulty with self-referential cleanup (object A's destructor creates object B)
- Assumes destructor doesn't throw (C has no exception safety guarantees)

**Success Criteria:**
- All objects destroyed exactly once on all code paths
- Cleanup happens in reverse construction order (stack discipline)
- No memory leaks, no double-frees
- Verifiable via static analysis or AddressSanitizer on generated C

</implementation_notes>

</feature>

<feature name="Exceptions">

<c_representation>

### C Representation: PNaCl-Style SJLJ (Proven Pattern)

**UPDATE v1.2:** Historical research reveals the proven implementation pattern used by Comeau C++, EDG, and PNaCl.

**The Proven Approach: SJLJ with Action Tables**

Historical compilers (1990s-2013) validated this pattern in production. PNaCl (2013) provides the definitive modern implementation with thread-safety.

```cpp
// C++ Input
void mayThrow() {
    if (error) {
        throw std::runtime_error("Error occurred");
    }
}

void caller() {
    try {
        Resource r;
        mayThrow();
        useResource(r);
    } catch (const std::runtime_error& e) {
        std::cerr << "Caught: " << e.what() << std::endl;
    }
}
```

```c
// Generated C (PNaCl-style SJLJ with action tables)

// Action table entry (describes one destructor call)
struct __cxx_action_entry {
    void (*destructor)(void*);  // Destructor function
    void* object;                // Object to destroy
};

// Exception frame (one per try block, NOT per scope)
struct __cxx_exception_frame {
    jmp_buf jmpbuf;                           // setjmp/longjmp state
    struct __cxx_exception_frame* next;        // Stack of active frames
    const struct __cxx_action_entry* actions;  // Destructor sequence
    void* exception_object;                    // Current exception
};

// Thread-local exception state (CRITICAL: must be thread-local)
_Thread_local struct __cxx_exception_frame* __cxx_exception_stack = NULL;

// Throw mechanism with unwinding
void __cxx_throw(void* exception_obj) {
    if (__cxx_exception_stack == NULL) {
        abort();  // Uncaught exception
    }

    // Two-phase unwinding: call destructors, then jump
    const struct __cxx_action_entry* action = __cxx_exception_stack->actions;
    while (action && action->destructor) {
        action->destructor(action->object);  // Call destructor
        action++;
    }

    // Store exception and jump to catch
    __cxx_exception_stack->exception_object = exception_obj;
    longjmp(__cxx_exception_stack->jmpbuf, 1);
}

// Generated code for caller()
void caller(void) {
    Resource r;

    // Action table for this scope (static, compiler-generated)
    static const struct __cxx_action_entry caller_actions[] = {
        { (void(*)(void*))&Resource__dtor, &r },
        { NULL, NULL }  // Terminator
    };

    Resource__ctor(&r);

    // Exception frame for try block
    struct __cxx_exception_frame frame;
    frame.next = __cxx_exception_stack;
    frame.actions = caller_actions;
    frame.exception_object = NULL;

    if (setjmp(frame.jmpbuf) == 0) {
        __cxx_exception_stack = &frame;  // Push frame

        mayThrow();  // Might throw
        useResource(&r);

        __cxx_exception_stack = frame.next;  // Pop frame
    } else {
        // Catch block (destructors already called during unwinding)
        RuntimeError* e = (RuntimeError*)frame.exception_object;
        fprintf(stderr, "Caught: %s\n", RuntimeError_what(e));
        RuntimeError_destroy(e);
        free(e);
    }

    // Normal cleanup
    Resource__dtor(&r);
}
```

**Key Innovation: Action Tables**

Action tables eliminate "nested setjmp at every scope". Instead:
- ONE exception frame per try block
- Action table describes ALL destructors in scope
- Unwinding walks action table, no nested setjmp needed

**Historical Validation:**
- Comeau C++ (1990s): Proved SJLJ works in production
- PNaCl (2013): Added thread-safety with _Thread_local
- Still used in Emscripten for WebAssembly exception support

**Approach 2: Error Codes (More idiomatic C)**

```c
// Generated C (error code approach)

typedef enum {
    OK = 0,
    ERROR_RUNTIME = 1,
    ERROR_INVALID_ARGUMENT = 2,
    // ... other error codes
} ErrorCode;

// Functions return error codes
ErrorCode mayThrow(void) {
    if (error) {
        return ERROR_RUNTIME;
    }
    return OK;
}

ErrorCode caller(void) {
    Resource r;
    Resource_init(&r);

    ErrorCode err = mayThrow();
    if (err != OK) {
        // Error handling
        fprintf(stderr, "Error occurred: %d\n", err);
        Resource_destroy(&r);
        return err;
    }

    err = useResource(&r);
    Resource_destroy(&r);

    return err;
}
```

</c_representation>

<complexity>Extreme</complexity>

<feasibility>Severe Limitations</feasibility>

<implementation_notes>

**Why Exceptions Are Hard in C:**

1. **No Built-in Stack Unwinding:**
   - C++ compiler generates cleanup code automatically
   - C requires manual cleanup at every error point
   - setjmp/longjmp provides non-local jumps but no automatic cleanup

2. **RAII Interaction:**
   - Exception + RAII = automatic resource cleanup during unwinding
   - setjmp/longjmp bypasses normal function returns, skipping cleanup
   - Must manually inject cleanup code between setjmp and longjmp

3. **Type System Mismatch:**
   - C++ exceptions are typed (catch different exception types)
   - C has no type-safe way to represent "any exception type"
   - Options: void* (unsafe), union of all exception types (verbose), integer error codes (loss of information)

**setjmp/longjmp Approach Problems:**

**Problem 1: RAII Cleanup During Unwinding**

```c
void functionWithRAII(void) {
    ExceptionFrame frame;
    exception_stack = &frame;

    Resource r1;
    Resource_init(&r1);

    if (setjmp(frame.jump_buffer) == 0) {
        Resource r2;
        Resource_init(&r2);

        mayThrow();  // Might longjmp

        Resource_destroy(&r2);  // ← Skipped if longjmp occurs!
    } else {
        // Catch: r2 was NOT cleaned up!
        // Must manually track and cleanup
    }

    Resource_destroy(&r1);
}
```

**Solution:** Every scope with RAII objects needs nested setjmp:

```c
void functionWithRAII(void) {
    ExceptionFrame frame1;
    Resource r1;

    frame1.prev = exception_stack;
    exception_stack = &frame1;
    Resource_init(&r1);

    if (setjmp(frame1.jump_buffer) == 0) {
        ExceptionFrame frame2;
        Resource r2;

        frame2.prev = exception_stack;
        exception_stack = &frame2;
        Resource_init(&r2);

        if (setjmp(frame2.jump_buffer) == 0) {
            mayThrow();
            Resource_destroy(&r2);
        } else {
            // Clean up r2, then re-throw
            Resource_destroy(&r2);
            exception_stack = frame2.prev;
            longjmp(frame1.jump_buffer, 1);
        }

        exception_stack = frame2.prev;
        Resource_destroy(&r2);
    } else {
        // Clean up r1
        Resource_destroy(&r1);
        exception_stack = frame1.prev;
        rethrow_if_needed();
    }

    exception_stack = frame1.prev;
    Resource_destroy(&r1);
}
```

**This is EXTREMELY verbose and error-prone!**

**Problem 2: Performance**

- setjmp is expensive (saves entire register context)
- Every function that might throw or has RAII needs setjmp
- Zero-cost exception model in C++ has no overhead when exceptions aren't thrown
- setjmp/longjmp has overhead on EVERY function call

**Problem 3: Exception Object Lifetime**

```cpp
class MyException : public std::exception {
    std::string message;  // Dynamic memory!
public:
    MyException(const char* msg) : message(msg) {}
};

throw MyException("Error");  // C++ manages lifetime
```

```c
// C equivalent:
typedef struct MyException {
    char* message;  // Who allocates? Who frees?
} MyException;

void throw_MyException(const char* msg) {
    MyException* ex = malloc(sizeof(MyException));
    ex->message = strdup(msg);
    throw_exception(ex);  // Caller must free!
}

// In catch:
MyException* ex = (MyException*)frame.exception_object;
// ... use ex ...
free(ex->message);
free(ex);
```

**Ownership tracking becomes complex!**

**Error Code Approach Problems:**

**Problem 1: Boilerplate**

Every function call requires error checking:

```c
ErrorCode err = func1();
if (err != OK) { cleanup(); return err; }

err = func2();
if (err != OK) { cleanup(); return err; }

err = func3();
if (err != OK) { cleanup(); return err; }
```

**Problem 2: Loss of Exception Information**

```cpp
// C++: Rich exception objects
throw DatabaseError("Connection failed", error_code, server_address);

// C: Just error codes
return ERROR_DATABASE;  // Lost details!
```

**Problem 3: Cannot Represent Multiple Return Values**

```cpp
// C++
int compute() {
    if (error) throw MyException();
    return result;  // Function returns value
}

// C: Either return value OR error, not both
int compute(int* result) {
    if (error) return ERROR_CODE;
    *result = computation;
    return OK;
}
```

**Clang APIs for Exception Handling:**

- `CXXTryStmt` - Try block
- `CXXCatchStmt` - Catch clause
- `CXXThrowExpr` - Throw expression
- `FunctionDecl::getExceptionSpecType()` - noexcept, throw() specs

**Recommendation:**

**For Readable C Code:** **Use error codes**, not setjmp/longjmp

**Rationale:**
- Error codes are idiomatic C
- More performant (no setjmp overhead)
- Easier to understand and maintain
- Explicit error handling (C philosophy)

**Conversion Strategy:**
```cpp
// C++ exception
throw std::runtime_error("Failed");

// Becomes C error code
return ERROR_RUNTIME;

// Try-catch becomes if-check
try { func(); } catch(...) { handle(); }

// Becomes:
ErrorCode err = func();
if (err != OK) { handle(); }
```

**Document Limitation:** "Exceptions are converted to error codes. Original exception messages and types are lost. Rich exception hierarchies flattened to error enum."

</implementation_notes>

</feature>

<feature name="STL (Standard Template Library)">

<c_representation>

### C Representation: Reimplement or Link C++ Runtime

**Three Approaches:**

**Approach 1: Link against C++ standard library (Pragmatic)**

```c
// Generated C code that links with libstdc++ or libc++
#ifdef __cplusplus
extern "C" {
#endif

// Opaque pointers to C++ STL types
typedef struct std_vector_int std_vector_int;
typedef struct std_string std_string;
typedef struct std_map_string_int std_map_string_int;

// Wrapper functions calling C++ STL
std_vector_int* std_vector_int_new(void);
void std_vector_int_delete(std_vector_int* vec);
void std_vector_int_push_back(std_vector_int* vec, int value);
int std_vector_int_at(const std_vector_int* vec, size_t index);
size_t std_vector_int_size(const std_vector_int* vec);

#ifdef __cplusplus
}

// C++ implementation (compiled as C++)
#include <vector>

extern "C" std_vector_int* std_vector_int_new(void) {
    return reinterpret_cast<std_vector_int*>(new std::vector<int>());
}

extern "C" void std_vector_int_delete(std_vector_int* vec) {
    delete reinterpret_cast<std::vector<int>*>(vec);
}

extern "C" void std_vector_int_push_back(std_vector_int* vec, int value) {
    reinterpret_cast<std::vector<int>*>(vec)->push_back(value);
}
// ... etc
#endif
```

**Approach 2: C reimplementation (Pure C, but massive effort)**

```c
// C reimplementation of std::vector<int>
typedef struct vector_int {
    int* data;
    size_t size;
    size_t capacity;
} vector_int;

void vector_int_init(vector_int* v) {
    v->data = NULL;
    v->size = 0;
    v->capacity = 0;
}

void vector_int_push_back(vector_int* v, int value) {
    if (v->size >= v->capacity) {
        size_t new_cap = v->capacity == 0 ? 8 : v->capacity * 2;
        int* new_data = realloc(v->data, new_cap * sizeof(int));
        if (new_data == NULL) abort();  // Out of memory
        v->data = new_data;
        v->capacity = new_cap;
    }
    v->data[v->size++] = value;
}

int vector_int_at(const vector_int* v, size_t index) {
    assert(index < v->size);
    return v->data[index];
}

void vector_int_destroy(vector_int* v) {
    free(v->data);
    v->data = NULL;
    v->size = v->capacity = 0;
}
```

**Approach 3: Use existing C libraries**

```c
// Use GLib, or other C data structure libraries
#include <glib.h>

// std::vector<int> → GArray
GArray* vec = g_array_new(FALSE, FALSE, sizeof(int));
int value = 42;
g_array_append_val(vec, value);
int retrieved = g_array_index(vec, int, 0);
g_array_free(vec, TRUE);

// std::map<string, int> → GHashTable
GHashTable* map = g_hash_table_new_full(g_str_hash, g_str_equal, g_free, NULL);
g_hash_table_insert(map, g_strdup("key"), GINT_TO_POINTER(42));
int* result = (int*)g_hash_table_lookup(map, "key");
g_hash_table_destroy(map);
```

</c_representation>

<complexity>Extreme (for full reimplementation)</complexity>

<feasibility>Impractical for pure C, pragmatic with C++ linkage</feasibility>

<implementation_notes>

**Why STL is Extremely Difficult:**

1. **Massive API Surface:**
   - Containers: vector, list, deque, set, map, unordered_set, unordered_map, array, forward_list
   - Algorithms: sort, find, binary_search, transform, accumulate, etc. (100+ algorithms)
   - Iterators: input, output, forward, bidirectional, random access
   - Utilities: pair, tuple, optional, variant, any, function
   - String: std::string, std::string_view
   - Smart pointers: unique_ptr, shared_ptr, weak_ptr

2. **Template Instantiation Explosion:**
   ```cpp
   std::vector<int>         // Needs C implementation
   std::vector<double>      // Needs separate C implementation
   std::vector<MyClass>     // Needs another C implementation
   std::vector<std::string> // Needs yet another, depends on std::string!
   ```

3. **Complex Semantics:**
   - Exception safety guarantees (strong, basic, nothrow)
   - Iterator invalidation rules
   - Move semantics for efficiency
   - Allocator support for custom memory management

**Recommended Strategy: PRAGMATIC SUBSET**

**Tier 1: Must Support (Core Containers)**
- `std::vector<T>` → Generate C vector for each T (monomorphization)
- `std::string` → Custom C string struct or link against C++ runtime
- `std::array<T, N>` → C array with helper functions

**Tier 2: Nice to Have**
- `std::map<K, V>` → Use C libraries (GLib's GHashTable, khash, etc.) or link C++ runtime
- `std::unordered_map<K, V>` → Same as map
- `std::pair<T1, T2>` → C struct with two members

**Tier 3: Unsupported (Document Alternatives)**
- Smart pointers → Manual memory management with clear ownership rules
- Complex algorithms → Implement case-by-case or use C libraries
- Iterators → Pointers or indices
- std::function → Function pointers (no capture)
- std::optional, std::variant → Custom tagged unions

**Clang APIs:**

- `ClassTemplateSpecializationDecl` - Identify STL container instantiations
- Check if type's declaration is in `std::` namespace
- Extract template arguments to determine monomorphization needed

**Code Generation Pattern:**

```python
def handle_stl_vector(template_args):
    element_type = template_args[0]

    if is_primitive(element_type):
        # Generate simple C vector
        generate_c_vector(element_type)
    elif is_user_class(element_type):
        # Generate vector with init/destroy calls for elements
        generate_c_vector_with_lifecycle(element_type)
    elif is_stl_type(element_type):
        # Nested STL (e.g., vector<vector<int>>)
        # Recursively generate inner type first
        handle_stl_type(element_type)
        generate_c_vector(element_type)
```

**Realistic Assessment:**

Reimplementing full STL in C is **equivalent to rewriting libc++/libstdc++** - person-years of effort.

**Viable Alternatives:**
1. **Link C++ runtime**: Generated C code calls into libstdc++ via wrapper functions
2. **Partial reimplementation**: Vector, string, simple types only
3. **Use C libraries**: GLib for containers, better string library, etc.
4. **Require STL avoidance**: Target C++ subset without STL (embedded-friendly)

</implementation_notes>

</feature>

<feature name="Lambdas and Closures">

<c_representation>

### C Representation: Closure Structs + Function Pointers

```cpp
// C++ Input
void processData(const std::vector<int>& data) {
    int multiplier = 5;

    // Capturing lambda
    auto transform = [multiplier](int x) {
        return x * multiplier;
    };

    for (int value : data) {
        std::cout << transform(value) << std::endl;
    }
}

// Generic lambda (C++14)
auto generic = [](auto x, auto y) {
    return x + y;
};
```

```c
// Generated C Output

// Closure struct for captured variables
typedef struct {
    int multiplier;
} Closure_transform;

// Lambda function becomes static function
static int lambda_transform(Closure_transform* closure, int x) {
    return x * closure->multiplier;
}

void processData(const vector_int* data) {
    int multiplier = 5;

    // Initialize closure
    Closure_transform closure = { .multiplier = multiplier };

    for (size_t i = 0; i < vector_int_size(data); i++) {
        int value = vector_int_at(data, i);
        int result = lambda_transform(&closure, value);
        printf("%d\n", result);
    }
}

// Generic lambda → Monomorphize for each used type combination
static int lambda_generic_int_int(int x, int y) {
    return x + y;
}

static double lambda_generic_double_double(double x, double y) {
    return x + y;
}
```

**Captureless Lambda → Function Pointer:**

```cpp
// C++ captureless lambda
auto comparator = [](int a, int b) { return a < b; };

// Can be converted to function pointer
int (*comp_ptr)(int, int) = comparator;
```

```c
// Generated C
static int lambda_comparator(int a, int b) {
    return a < b;
}

// Direct function pointer, no closure needed
int (*comp_ptr)(int, int) = lambda_comparator;
```

</c_representation>

<complexity>Medium</complexity>

<feasibility>Straightforward for common cases, challenging for complex captures</feasibility>

<implementation_notes>

**How Lambda Conversion Works:**

1. **Identify Lambda in AST**: `LambdaExpr` node
2. **Extract Capture List**: `LambdaExpr::captures()`
3. **Generate Closure Struct**: One struct field per captured variable
4. **Generate Function**: Static function taking closure pointer + original parameters
5. **Replace Lambda Call**: Pass closure struct to generated function

**Clang APIs:**
- `LambdaExpr` - AST node for lambda expression
- `LambdaExpr::captures()` - Get list of captured variables
- `LambdaExpr::getCaptureKind()` - By value vs by reference
- `LambdaExpr::getCallOperator()` - Get the operator() method
- `LambdaExpr::isMutable()` - Check if lambda is mutable

**Capture Modes:**

**Capture by Value:**
```cpp
int x = 5;
auto f = [x]() { return x * 2; };  // Copy x
```

```c
typedef struct { int x; } Closure_f;

static int lambda_f(Closure_f* closure) {
    return closure->x * 2;
}

// Usage:
Closure_f closure = { .x = x };
int result = lambda_f(&closure);
```

**Capture by Reference:**
```cpp
int x = 5;
auto f = [&x]() { x *= 2; return x; };  // Reference to x
```

```c
typedef struct { int* x; } Closure_f;  // Pointer for reference

static int lambda_f(Closure_f* closure) {
    *closure->x *= 2;
    return *closure->x;
}

// Usage:
Closure_f closure = { .x = &x };
int result = lambda_f(&closure);
x;  // Now equals 10 (modified through reference)
```

**Mutable Lambda:**
```cpp
int x = 5;
auto f = [x]() mutable { return ++x; };  // Can modify captured copy
```

```c
typedef struct { int x; } Closure_f;

static int lambda_f(Closure_f* closure) {
    return ++closure->x;  // Modifies closure, not original
}
```

**Challenges:**

**1. Generic Lambdas (C++14):**
```cpp
auto f = [](auto x) { return x * 2; };
f(5);      // Calls operator()<int>
f(3.14);   // Calls operator()<double>
```
- Solution: Monomorphize like templates
- Generate separate C functions for each used type

**2. Std::function (Type Erasure):**
```cpp
std::function<int(int)> func = [x](int y) { return x + y; };
```
- C has no type erasure
- Options:
  - Void pointer + function pointer (unsafe, requires casting)
  - Generate specific wrapper types
  - Limit to function pointers only (no capture)

**3. Returning Lambdas (Closure Lifetime):**
```cpp
auto makeAdder(int x) {
    return [x](int y) { return x + y; };  // Closure captures x
}

auto adder = makeAdder(5);
int result = adder(10);  // 15
```

```c
// C version needs heap allocation for closure
typedef struct { int x; } Closure_adder;

static int lambda_adder(Closure_adder* closure, int y) {
    return closure->x + y;
}

Closure_adder* makeAdder(int x) {
    Closure_adder* closure = malloc(sizeof(Closure_adder));
    closure->x = x;
    return closure;  // Caller must free!
}

// Usage:
Closure_adder* adder = makeAdder(5);
int result = lambda_adder(adder, 10);
free(adder);  // Manual memory management
```

**4. Lambda in Capture:**
```cpp
auto outer = [x = 5]() {
    auto inner = [x]() { return x * 2; };
    return inner();
};
```
- Nested closures → nested structs
- Complexity grows quickly

**Success Criteria:**
- Simple lambdas (value/reference capture, no nesting) converted correctly
- Captureless lambdas become simple function pointers
- Generic lambdas monomorphized for used types
- **Limitation**: std::function not supported, returning lambdas requires manual memory management

</implementation_notes>

</feature>

<feature name="Move Semantics and Rvalue References">

<c_representation>

### C Representation: Explicit Transfer Functions

```cpp
// C++ Input
class Buffer {
    char* data;
    size_t size;
public:
    Buffer(size_t s) : data(new char[s]), size(s) {}
    ~Buffer() { delete[] data; }

    // Move constructor
    Buffer(Buffer&& other) noexcept
        : data(other.data), size(other.size)
    {
        other.data = nullptr;  // Transfer ownership
        other.size = 0;
    }

    // Move assignment
    Buffer& operator=(Buffer&& other) noexcept {
        if (this != &other) {
            delete[] data;
            data = other.data;
            size = other.size;
            other.data = nullptr;
            other.size = 0;
        }
        return *this;
    }
};

Buffer createBuffer() {
    Buffer b(1024);
    return b;  // Move, not copy
}
```

```c
// Generated C Output

typedef struct Buffer {
    char* data;
    size_t size;
} Buffer;

// Regular constructor
void Buffer_init(Buffer* this, size_t s) {
    this->data = (char*)malloc(s);
    this->size = s;
}

// Destructor
void Buffer_destroy(Buffer* this) {
    free(this->data);
    this->data = NULL;
    this->size = 0;
}

// Move "constructor" → transfer function
void Buffer_move_init(Buffer* this, Buffer* source) {
    this->data = source->data;
    this->size = source->size;

    // Leave source in valid but empty state
    source->data = NULL;
    source->size = 0;
}

// Move assignment
void Buffer_move_assign(Buffer* this, Buffer* source) {
    if (this != source) {
        // Destroy current contents
        free(this->data);

        // Transfer from source
        this->data = source->data;
        this->size = source->size;

        // Clear source
        source->data = NULL;
        source->size = 0;
    }
}

Buffer createBuffer(void) {
    Buffer b;
    Buffer_init(&b, 1024);
    // C returns by value (copy), not move
    // Compiler may optimize (RVO), but not guaranteed
    return b;
}

// Alternative: Return via out-parameter for explicit transfer
void createBuffer_transfer(Buffer* out) {
    Buffer_init(out, 1024);
    // Ownership transferred to caller
}
```

</c_representation>

<complexity>Low to Medium</complexity>

<feasibility>Straightforward - becomes explicit ownership transfer</feasibility>

<implementation_notes>

**Key Insight:** Move semantics is an **optimization** and **ownership transfer** mechanism. In C, ownership transfer is explicit via function naming and documentation.

**What C++ Move Semantics Provides:**
1. **Performance**: Avoid deep copies for temporaries
2. **Ownership transfer**: Make it clear when ownership moves
3. **Compiler optimization**: Rvalue references enable move operations
4. **Standard library support**: Move-aware containers

**C Equivalent Patterns:**

**Pattern 1: Explicit Transfer Functions**

```c
// Instead of move constructor/assignment
void MyType_transfer(MyType* dest, MyType* source);

// Clear naming convention:
void Widget_move_to(Widget* this, Widget* dest);
void Widget_take_from(Widget* this, Widget* source);
```

**Pattern 2: Return via Out-Parameter**

```c
// C++ returns by move
Buffer createBuffer() { return Buffer(1024); }

// C uses out-parameter for ownership transfer
void createBuffer(Buffer* out) {
    Buffer_init(out, 1024);
}
```

**Pattern 3: Swap-based Idiom**

```c
// Swap for move-assignment equivalent
void Buffer_swap(Buffer* a, Buffer* b) {
    Buffer temp = *a;
    *a = *b;
    *b = temp;
}

void Buffer_move_assign(Buffer* this, Buffer* source) {
    Buffer temp = {0};  // Empty buffer
    Buffer_swap(source, &temp);  // Transfer source → temp
    Buffer_destroy(this);  // Destroy old contents
    *this = temp;  // Take ownership
}
```

**Clang APIs:**

- `CXXConstructExpr::isElidable()` - Check if copy elision applies
- `CXXConstructExpr::getConstructionKind()` - Complete vs delegating vs move
- `CXXMethodDecl::isMoveAssignmentOperator()` - Detect move assignment
- `FunctionDecl::getReturnType()` - Check for rvalue reference return

**Challenges:**

**1. Perfect Forwarding:**
```cpp
template<typename T>
void wrapper(T&& arg) {
    process(std::forward<T>(arg));  // Forward lvalue as lvalue, rvalue as rvalue
}
```
- C has no universal references
- Solution: Generate separate functions for lvalue/rvalue cases (if needed)
- Or: Ignore forwarding, always pass by pointer

**2. Implicit Move from Temporaries:**
```cpp
Buffer b = createBuffer();  // Move, not copy
```
- C++ compiler automatically moves from temporaries
- C must make it explicit:
```c
Buffer b;
createBuffer(&b);  // Explicit initialization
```

**3. std::move() Casts:**
```cpp
Buffer b1(1024);
Buffer b2 = std::move(b1);  // Explicit move
```

```c
Buffer b1;
Buffer_init(&b1, 1024);

Buffer b2;
Buffer_move_init(&b2, &b1);  // Explicit transfer
// b1 is now in moved-from state (valid but empty)
```

**Optimization Considerations:**

- C compilers may perform RVO (Return Value Optimization) without move semantics
- Modern C compilers optimize struct returns well
- Generated C code may be less efficient than C++ move semantics, but difference is often negligible

**Documentation Requirements:**

Generated C code should document:
- Which functions transfer ownership
- Preconditions (e.g., source must be valid)
- Postconditions (e.g., source left in valid but unspecified state)

**Success Criteria:**
- Move constructors → transfer/init functions
- Move assignment → transfer/assign functions
- Clear naming conventions indicate ownership transfer
- Documentation clarifies semantics

</implementation_notes>

</feature>

<feature name="Other Modern C++ Features">

<c_representation>

### Miscellaneous Modern Features

**`auto` Type Deduction:**
```cpp
auto x = 42;               // int
auto y = 3.14;             // double
auto z = std::string("hello");  // std::string
```

**C Conversion:** Trivial - Clang already resolved types in AST

```c
int x = 42;
double y = 3.14;
String z = String_from_cstr("hello");
```

**Range-based For Loop:**
```cpp
for (const auto& item : container) {
    process(item);
}
```

```c
// De-sugared to traditional for loop
for (size_t i = 0; i < container_size(&container); i++) {
    const Item* item = container_at(&container, i);
    process(item);
}
```

**`constexpr` Functions:**
```cpp
constexpr int square(int x) {
    return x * x;
}

int arr[square(5)];  // Compile-time evaluation
```

```c
// Clang evaluates constexpr during compilation
// Generate C constant
#define SQUARE_5 25
int arr[SQUARE_5];

// Or inline the value
int arr[25];
```

**`nullptr`:**
```cpp
void* ptr = nullptr;
```

```c
void* ptr = NULL;  // Or: ((void*)0)
```

**Scoped Enums:**
```cpp
enum class Color {
    Red,
    Green,
    Blue
};

Color c = Color::Red;
```

```c
typedef enum {
    Color_Red,
    Color_Green,
    Color_Blue
} Color;

Color c = Color_Red;
```

**Attributes:**
```cpp
[[nodiscard]] int compute();
[[maybe_unused]] int x = 5;
```

```c
// GCC/Clang attributes
__attribute__((warn_unused_result)) int compute(void);
__attribute__((unused)) int x = 5;
```

</c_representation>

<complexity>Low</complexity>

<feasibility>Straightforward</feasibility>

<implementation_notes>

**These features are relatively easy to convert because:**

1. **auto**: Type already resolved by Clang's semantic analysis
2. **Range-for**: Syntactic sugar, de-sugars to traditional loop
3. **constexpr**: Evaluated at compile-time, becomes constant
4. **nullptr**: Direct mapping to NULL
5. **Enum class**: Becomes C enum with prefixed names
6. **Attributes**: Map to compiler-specific __attribute__ or omit

**Clang APIs:**
- `QualType::getAsString()` - Get resolved type from `auto`
- `CXXForRangeStmt::getRangeInit()` - Get range expression
- `VarDecl::evaluateValue()` - Get compile-time constant value
- `EnumDecl::isScoped()` - Check if `enum class`

**Success Criteria:** All straightforward modern features convert correctly with minimal code generation

</implementation_notes>

</feature>

</feature_conversion_matrix>

## Additional Research Documents

**This research is split across multiple documents for organization:**

1. **This document:** Clang architecture, existing tools analysis, and feature conversion strategies
2. **feasibility-and-roadmap.md:** Comprehensive feasibility assessment, implementation roadmap, testing strategy, and risk analysis
3. **SUMMARY.md:** Executive summary for quick decision-making

All documents available in: `.prompts/001-clang-cpp-to-c-converter-research/`

</research_output>

