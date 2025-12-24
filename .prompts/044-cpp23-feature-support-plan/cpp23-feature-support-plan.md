# C++23 Feature Support Implementation Plan

**Target**: Improve C++23 support from **0%** to **20-25%** through systematic implementation of critical language features.

**Timeline**: 12-16 weeks (6 phases, 2-3 weeks each)

**Context**: Pipeline verification research (043) confirmed the three-stage transpiler architecture is sound (95% complete), but identified that 25% of Phase 33 failures stem from missing C++23 transformation visitors. This plan provides an incremental roadmap to add these features while maintaining code quality.

---

## Executive Summary

### Architecture Foundation

The cpptoc transpiler uses a proven three-stage architecture:

1. **Stage 1: Clang Parsing** (✅ Complete) - C++ source → Clang C++ AST
2. **Stage 2: Transformation** (⚠️ Partial) - C++ AST → C AST via RecursiveASTVisitor
3. **Stage 3: Emission** (✅ Complete) - C AST → C99 code via CodeGenerator

**Existing successful transformations** (to learn from):
- Classes → Structs (VisitCXXRecordDecl)
- Virtual functions → Vtables (VirtualMethodAnalyzer, VtableGenerator)
- Templates → Monomorphization (TemplateExtractor, TemplateMonomorphizer)
- Exceptions → setjmp/longjmp (TryCatchTransformer, ThrowTranslator)
- Move semantics → Explicit copy/swap (MoveConstructorTranslator, MoveAssignmentTranslator)

### Implementation Strategy

**Key architectural patterns** (proven by existing code):

```
Pattern 1: Visitor Registration
  └─ Add Visit method to CppToCVisitor
  └─ Register handler instance as member
  └─ Route AST node to handler

Pattern 2: Handler Implementation
  └─ Create {Feature}Translator class
  └─ Implement transform() method
  └─ Use CNodeBuilder to create C AST nodes

Pattern 3: Testing Validation
  └─ Write unit tests with AST matching
  └─ Run relevant Phase 33 tests
  └─ A/B test C output against C++ version
```

**File modification pattern**:
```
New files:
  include/{Feature}Translator.h    (Handler interface)
  src/{Feature}Translator.cpp      (Transformation logic)
  tests/{Feature}TranslatorTest.cpp (Unit tests)

Modified files:
  include/CppToCVisitor.h          (Add Visit method declaration)
  src/CppToCVisitor.cpp            (Implement Visit method)
  include/CNodeBuilder.h           (Extend if new C patterns needed)
```

---

## C++23 Feature Catalog

Based on Phase 33 test analysis and C++ standard papers:

### Priority 1: High Impact (Must Have)

<feature>
  <id>1</id>
  <name>Deducing This (P0847R7)</name>
  <test-count>22</test-count>
  <impact>High - enables unified call syntax, recursive lambdas, CRTP simplification</impact>
  <complexity>Medium - requires overload expansion</complexity>

  <cpp-syntax>
    ```cpp
    struct TextBuffer {
        std::string data;

        // Explicit object parameter - unified for all cv-ref qualifiers
        auto& get(this auto& self) {
            return self.data;
        }
    };

    TextBuffer buf;
    buf.get();           // Calls with lvalue
    TextBuffer{}.get();  // Calls with rvalue
    ```
  </cpp-syntax>

  <c-equivalent>
    ```c
    struct TextBuffer {
        char* data;
    };

    // Expanded to 4 overloads
    char* TextBuffer__get(struct TextBuffer* self) {
        return self->data;
    }

    const char* TextBuffer__get_const(const struct TextBuffer* self) {
        return self->data;
    }

    // Note: C99 doesn't have rvalue refs, but we can provide value-based version
    char* TextBuffer__get_rvalue(struct TextBuffer* self) {
        return self->data;
    }
    ```
  </c-equivalent>

  <ast-pattern>
    CXXMethodDecl with explicit object parameter:
    - Check: Method->isExplicitObjectMemberFunction()
    - Get param: Method->getParamDecl(0) with 'this' specifier
    - Deduce type: ParmVarDecl with auto/decltype(auto) type
    - Match pattern: 'this {auto|const auto|auto&|const auto&|auto&&}& self'
  </ast-pattern>

  <transformation-strategy>
    1. Detect explicit object parameter methods
    2. Analyze template parameter constraints (auto deduction)
    3. Generate 4 overloads:
       - Non-const lvalue: T* (or T&)
       - Const lvalue: const T*
       - Non-const rvalue: T* (best effort in C)
       - Const rvalue: const T* (best effort in C)
    4. Mangle names distinctly (_lvalue, _const, _rvalue)
    5. For recursive lambdas: convert to named helper function
  </transformation-strategy>

  <edge-cases>
    - Recursive lambdas: Extract to named function, pass function pointer
    - CRTP usage: Expand template and generate overloads
    - Forwarding references (auto&&): Map to both lvalue and rvalue versions
    - Constraints on auto: Evaluate at transpile time or emit all overloads
  </edge-cases>
</feature>

<feature>
  <id>2</id>
  <name>if consteval (P1938R3)</name>
  <test-count>13</test-count>
  <impact>Medium - enables runtime/compile-time dual paths</impact>
  <complexity>High - requires compile-time evaluation capability</complexity>

  <cpp-syntax>
    ```cpp
    int flexible_compute(int x) {
        if consteval {
            // Compile-time path
            return x * x;
        } else {
            // Runtime path
            return compute_runtime(x);
        }
    }

    constexpr int ct = flexible_compute(5);  // Uses consteval path
    int rt = flexible_compute(x);            // Uses runtime path
    ```
  </cpp-syntax>

  <c-equivalent>
    ```c
    // Option 1: Macro-based (simple cases)
    #define FLEXIBLE_COMPUTE_CT(x) ((x) * (x))
    int flexible_compute_runtime(int x) {
        return compute_runtime(x);
    }

    // Option 2: Runtime-only fallback
    int flexible_compute(int x) {
        // Always use runtime path in C
        return compute_runtime(x);
    }
    ```
  </c-equivalent>

  <ast-pattern>
    IfStmt with consteval condition:
    - Check: isa&lt;ConstEvalIfStmt&gt;(S)
    - Or check: IfStmt->isConsteval()
    - Get then-branch: Compile-time code
    - Get else-branch: Runtime code
  </ast-pattern>

  <transformation-strategy>
    1. Detect if consteval statement
    2. Check usage context:
       - In constexpr function called at compile-time → emit consteval branch
       - In constexpr function called at runtime → emit else branch
       - In regular function → emit else branch only
    3. For simple cases: Generate macro for compile-time path
    4. For complex cases: Emit runtime path with comment documenting compile-time behavior
    5. Warn user if compile-time optimization lost
  </transformation-strategy>

  <edge-cases>
    - Nested if consteval: Recursively evaluate outer context
    - if !consteval: Invert branch logic
    - Used with immediate functions: Requires whole-program analysis
    - Side effects in consteval branch: Must ensure not executed at runtime
  </edge-cases>
</feature>

<feature>
  <id>3</id>
  <name>Multidimensional Subscript Operator (P2128R6)</name>
  <test-count>16</test-count>
  <impact>Medium - enables natural matrix/tensor syntax</impact>
  <complexity>Low - straightforward function conversion</complexity>

  <cpp-syntax>
    ```cpp
    template&lt;typename T&gt;
    struct Matrix {
        T& operator[](size_t row, size_t col) {
            return data[row * cols + col];
        }

        const T& operator[](size_t row, size_t col) const {
            return data[row * cols + col];
        }

        T* data;
        size_t rows, cols;
    };

    Matrix&lt;int&gt; m(3, 3);
    m[1, 2] = 42;  // Multi-arg subscript
    ```
  </cpp-syntax>

  <c-equivalent>
    ```c
    struct Matrix_int {
        int* data;
        size_t rows, cols;
    };

    int* Matrix_int__subscript(struct Matrix_int* self, size_t row, size_t col) {
        return &self->data[row * self->cols + col];
    }

    const int* Matrix_int__subscript_const(const struct Matrix_int* self,
                                           size_t row, size_t col) {
        return &self->data[row * self->cols + col];
    }

    // Usage
    struct Matrix_int m;
    *Matrix_int__subscript(&m, 1, 2) = 42;
    ```
  </c-equivalent>

  <ast-pattern>
    CXXOperatorCallExpr with OO_Subscript and multiple arguments:
    - Check: Call->getOperator() == OO_Subscript
    - Check: Call->getNumArgs() &gt; 2 (object + 2+ indices)
    - Extract indices: Call->getArg(1), Call->getArg(2), ...
    - Get method: cast to CXXMethodDecl
  </ast-pattern>

  <transformation-strategy>
    1. Detect operator[] with multiple parameters
    2. Convert to named function: {Class}__{op}_subscript_multidim
    3. Generate const and non-const versions
    4. For lvalue usage: Return pointer to allow assignment
    5. For rvalue usage: Return value directly
    6. For variadic subscript: Generate function with max arity encountered
  </transformation-strategy>

  <edge-cases>
    - Mixed with single-arg operator[]: Generate both versions
    - Variadic subscript operator[](auto... indices): Cap at reasonable arity (e.g., 4)
    - Static operator[]: Convert to static function
    - Chained subscript: m[i,j][k] → requires multi-step translation
  </edge-cases>
</feature>

### Priority 2: Medium Impact (Should Have)

<feature>
  <id>4</id>
  <name>Static operator() and operator[] (P1169R4)</name>
  <test-count>8</test-count>
  <impact>Low - convenience feature for function objects</impact>
  <complexity>Low - simple static function conversion</complexity>

  <cpp-syntax>
    ```cpp
    struct Calculator {
        static int operator()(int a, int b) {
            return a + b;
        }

        static int operator[](int x) {
            return x * x;
        }
    };

    Calculator calc;
    int sum = calc(5, 3);     // Static operator()
    int sq = calc[7];         // Static operator[]
    ```
  </cpp-syntax>

  <c-equivalent>
    ```c
    struct Calculator {
        // Empty struct or single dummy field
        int _dummy;
    };

    static int Calculator__call_static(int a, int b) {
        return a + b;
    }

    static int Calculator__subscript_static(int x) {
        return x * x;
    }

    // Usage
    struct Calculator calc;
    int sum = Calculator__call_static(5, 3);
    int sq = Calculator__subscript_static(7);
    ```
  </c-equivalent>

  <ast-pattern>
    CXXMethodDecl for operator() or operator[] with static qualifier:
    - Check: Method->isStatic()
    - Check: Method->isOverloadedOperator()
    - Check: Method->getOverloadedOperator() in {OO_Call, OO_Subscript}
  </ast-pattern>

  <transformation-strategy>
    1. Detect static operator methods
    2. Convert to static free function: {Class}__{op}_static
    3. Remove implicit 'this' parameter
    4. Transform call sites: obj.operator()(args) → {Class}__call_static(args)
    5. For operator[]: Transform obj[idx] → {Class}__subscript_static(idx)
  </transformation-strategy>

  <edge-cases>
    - Combined with non-static operator(): Generate both versions
    - Combined with multidim subscript: Generate all variants
    - Template operator: Monomorphize first, then convert
  </edge-cases>
</feature>

<feature>
  <id>5</id>
  <name>auto(x) and auto{x} Decay-Copy (P0849R8)</name>
  <test-count>22 (partial support needed)</test-count>
  <impact>Medium - affects generic code and forwarding</impact>
  <complexity>Medium - requires type deduction and copy semantics</complexity>

  <cpp-syntax>
    ```cpp
    void forward_value(auto&& x) {
        // Decay-copy: removes references, cv-qualifiers
        send(auto(x));   // Forces copy and decay
        send(auto{x});   // Same, with braced-init
    }

    const int& ref = getValue();
    auto copy = auto(ref);  // 'copy' is 'int', not 'const int&'
    ```
  </cpp-syntax>

  <c-equivalent>
    ```c
    void forward_value_int(int* x) {
        // Explicit decay-copy
        int decayed = *x;
        send(&decayed);
    }

    int getValue(void);
    const int* ref = ...;
    int copy = *ref;  // Manual decay-copy
    ```
  </c-equivalent>

  <ast-pattern>
    CXXFunctionalCastExpr or CXXTemporaryObjectExpr with auto:
    - Check: Cast->getTypeAsWritten() is AutoType
    - Check: Cast kind is decay-copy
    - Get source expr: Cast->getSubExpr()
    - Deduce decayed type: Remove refs, cv-qualifiers, array-to-pointer, function-to-pointer
  </ast-pattern>

  <transformation-strategy>
    1. Detect auto(x) or auto{x} expressions
    2. Determine source type: typeof(x)
    3. Compute decayed type:
       - Remove references: T&, T&& → T
       - Remove cv-qualifiers: const T, volatile T → T
       - Decay arrays: T[N] → T*
       - Decay functions: T() → T(*)()
    4. Generate explicit copy: temp_var = *x (if reference), or temp_var = x (if value)
    5. Use temp_var in place of auto(x)
  </transformation-strategy>

  <edge-cases>
    - Array decay: auto(arr) → pointer
    - Function decay: auto(func) → function pointer
    - Class types: Invoke copy constructor
    - Move-only types: Convert to explicit move (if supported)
  </edge-cases>
</feature>

### Priority 3: Lower Impact (Nice to Have)

<feature>
  <id>6</id>
  <name>[[assume]] Attribute (P1774R8)</name>
  <test-count>13</test-count>
  <impact>Low - compiler optimization hint</impact>
  <complexity>Very Low - strip or convert to comment</complexity>

  <cpp-syntax>
    ```cpp
    int divide(int a, int b) {
        [[assume(b != 0)]];
        return a / b;
    }
    ```
  </cpp-syntax>

  <c-equivalent>
    ```c
    // Option 1: Strip attribute entirely
    int divide(int a, int b) {
        return a / b;
    }

    // Option 2: Convert to comment
    int divide(int a, int b) {
        /* assume: b != 0 */
        return a / b;
    }

    // Option 3: Convert to compiler-specific hint (GCC/Clang)
    int divide(int a, int b) {
        __builtin_assume(b != 0);
        return a / b;
    }
    ```
  </c-equivalent>

  <ast-pattern>
    AttributedStmt with AssumeAttr:
    - Check: Stmt->getAttr&lt;AssumeAttr&gt;()
    - Extract condition: Attr->getAssumption()
    - Get underlying statement
  </ast-pattern>

  <transformation-strategy>
    1. Detect [[assume(condition)]] attribute
    2. Option A: Strip and emit comment documenting assumption
    3. Option B: Convert to __builtin_assume() if targeting GCC/Clang
    4. Option C: Generate assert() in debug builds, strip in release
    5. Preserve underlying statement unchanged
  </transformation-strategy>

  <edge-cases>
    - Complex conditions: May need to translate C++ expression to C
    - Side effects in condition: Warn and strip
    - Multiple assumes: Process each independently
  </edge-cases>
</feature>

<feature>
  <id>7</id>
  <name>Constexpr Enhancements (P2448R2, etc.)</name>
  <test-count>19</test-count>
  <impact>Medium - enables more compile-time computation</impact>
  <complexity>High - requires compile-time evaluation engine</complexity>

  <cpp-syntax>
    ```cpp
    constexpr std::string make_greeting(std::string_view name) {
        std::string greeting = "Hello, ";
        greeting += name;  // C++23: constexpr std::string::operator+=
        return greeting;
    }

    constexpr auto msg = make_greeting("World");  // Compile-time
    ```
  </cpp-syntax>

  <c-equivalent>
    ```c
    // Option 1: Compile-time macro (simple cases)
    #define MAKE_GREETING(name) "Hello, " name

    // Option 2: Runtime function (complex cases)
    char* make_greeting(const char* name) {
        size_t len = strlen(name) + 8;
        char* greeting = malloc(len);
        strcpy(greeting, "Hello, ");
        strcat(greeting, name);
        return greeting;
    }
    ```
  </c-equivalent>

  <ast-pattern>
    FunctionDecl with constexpr specifier and C++23 features:
    - Check: Func->isConstexpr()
    - Check: Uses std::string, std::vector, etc. in constexpr context
    - Check: Complex control flow (goto in constexpr)
    - Check: Try-catch in constexpr
  </ast-pattern>

  <transformation-strategy>
    1. Detect constexpr functions using C++23 features
    2. Check if function is called at compile-time:
       - Used in constant expression context
       - Result assigned to constexpr variable
    3. For compile-time calls:
       - Attempt to evaluate using Clang's constant evaluator
       - Emit result as literal in C code
    4. For runtime calls:
       - Convert to regular C function
       - Emit warning if compile-time optimization lost
    5. For complex cases: Fallback to runtime function
  </transformation-strategy>

  <edge-cases>
    - std::string in constexpr: Convert to string literals or runtime
    - std::vector in constexpr: Convert to arrays or runtime
    - Goto in constexpr: Complex control flow analysis
    - Try-catch in constexpr: Requires exception handling infrastructure
    - Non-literal types: Must evaluate at compile-time or error
  </edge-cases>
</feature>

<feature>
  <id>8</id>
  <name>CTAD with Inherited Constructors (P2582R1)</name>
  <test-count>10 (partial support)</test-count>
  <impact>Low - mostly impacts template instantiation</impact>
  <complexity>Medium - enhances existing template deduction</complexity>

  <cpp-syntax>
    ```cpp
    template&lt;typename T&gt;
    struct Base {
        Base(T val) : value(val) {}
        T value;
    };

    template&lt;typename T&gt;
    struct Derived : Base&lt;T&gt; {
        using Base&lt;T&gt;::Base;  // Inherit constructor
    };

    Derived d(42);  // C++23 CTAD: deduces Derived&lt;int&gt;
    ```
  </cpp-syntax>

  <c-equivalent>
    ```c
    struct Base_int {
        int value;
    };

    void Base_int__ctor(struct Base_int* self, int val) {
        self->value = val;
    }

    struct Derived_int {
        struct Base_int base;
    };

    void Derived_int__ctor(struct Derived_int* self, int val) {
        Base_int__ctor(&self->base, val);
    }

    struct Derived_int d;
    Derived_int__ctor(&d, 42);
    ```
  </c-equivalent>

  <ast-pattern>
    ClassTemplateSpecializationDecl with inherited constructors:
    - Check: Class->hasInheritedConstructor()
    - Get using-declaration: UsingDecl for constructors
    - Get base class: Class->bases()
    - Detect CTAD: DeducedTemplateSpecializationType
  </ast-pattern>

  <transformation-strategy>
    1. Detect inherited constructors (using Base::Base)
    2. During template monomorphization:
       - Generate explicit forwarding constructors in derived class
       - Each forwards to corresponding base constructor
    3. For CTAD:
       - Already handled by template monomorphization
       - Ensure deduction guides account for inherited ctors
    4. Transform constructor calls:
       - Derived d(args) → Derived__ctor(&d, args)
       - Base constructor called within derived ctor
  </transformation-strategy>

  <edge-cases>
    - Multiple inheritance: Generate ctors for each base
    - Virtual inheritance: Handle vptr initialization
    - Private/protected base ctors: Respect access specifiers
    - Deleted inherited ctors: Don't generate
  </edge-cases>
</feature>

---

## Implementation Phases

### Phase 1: Multidimensional Subscript Operator (Weeks 1-2)

<phase>
  <id>1</id>
  <name>Multidimensional Subscript Operator Support</name>
  <features>Feature #3: Multidimensional Subscript Operator (P2128R6)</features>
  <estimated-effort>2 weeks</estimated-effort>
  <expected-improvement>+3-4% C++23 support (16 tests)</expected-improvement>

  <rationale>
    Start with the simplest feature to validate the implementation workflow.
    This feature has clear 1:1 mapping (multi-arg operator[] → multi-arg function),
    no complex language semantics, and immediate validation through matrix tests.
  </rationale>

  <dependencies>
    - None (can start immediately)
    - Existing: CNodeBuilder, CppToCVisitor infrastructure
  </dependencies>

  <technical-approach>
    Week 1: Detection and Basic Transformation
    - Implement AST pattern matching in CppToCVisitor
    - Create MultidimSubscriptTranslator class
    - Handle basic 2D case (Matrix[i, j])

    Week 2: Complete Implementation and Testing
    - Handle 3D+ cases (Tensor[i, j, k, ...])
    - Implement const/non-const overloads
    - Handle lvalue/rvalue contexts
    - Full test suite
  </technical-approach>

  <files-to-create>
    include/MultidimSubscriptTranslator.h
    src/MultidimSubscriptTranslator.cpp
    tests/MultidimSubscriptTranslatorTest.cpp
  </files-to-create>

  <files-to-modify>
    include/CppToCVisitor.h (add VisitCXXOperatorCallExpr or enhance existing)
    src/CppToCVisitor.cpp (route subscript calls to handler)
    CMakeLists.txt (add new source/test files)
  </files-to-modify>

  <implementation-details>
    <step>
      <number>1</number>
      <description>AST Pattern Detection</description>
      <code>
        ```cpp
        // In CppToCVisitor.h
        bool VisitCXXOperatorCallExpr(clang::CXXOperatorCallExpr* E);
        std::unique_ptr&lt;MultidimSubscriptTranslator&gt; m_multidimSubscriptTrans;

        // In CppToCVisitor.cpp
        bool CppToCVisitor::VisitCXXOperatorCallExpr(CXXOperatorCallExpr* E) {
            if (E->getOperator() == OO_Subscript && E->getNumArgs() > 2) {
                // Multi-dimensional subscript: E->getArg(0) is object,
                // E->getArg(1..N-1) are indices
                auto C_Call = m_multidimSubscriptTrans->transform(E, Context, C_TranslationUnit);
                if (C_Call) {
                    // Replace in parent expression
                }
            }
            return true;
        }
        ```
      </code>
    </step>

    <step>
      <number>2</number>
      <description>Translator Implementation</description>
      <code>
        ```cpp
        // In MultidimSubscriptTranslator.h
        class MultidimSubscriptTranslator {
        public:
            MultidimSubscriptTranslator(CNodeBuilder& Builder);

            // Transform multi-arg subscript to function call
            clang::CallExpr* transform(clang::CXXOperatorCallExpr* E,
                                       clang::ASTContext& Ctx,
                                       clang::TranslationUnitDecl* C_TU);
        private:
            CNodeBuilder& Builder;

            // Generate function name: Matrix_int__subscript_2d
            std::string generateFunctionName(const CXXRecordDecl* Class,
                                            unsigned NumIndices,
                                            bool IsConst);

            // Create or reuse function declaration
            FunctionDecl* getOrCreateSubscriptFunction(
                const CXXOperatorCallExpr* E,
                clang::ASTContext& Ctx);
        };

        // In MultidimSubscriptTranslator.cpp
        CallExpr* MultidimSubscriptTranslator::transform(
            CXXOperatorCallExpr* E, ASTContext& Ctx, TranslationUnitDecl* C_TU) {

            // Get object and indices
            Expr* Object = E->getArg(0);
            std::vector&lt;Expr*&gt; Indices;
            for (unsigned i = 1; i < E->getNumArgs(); ++i) {
                Indices.push_back(E->getArg(i));
            }

            // Get or create function declaration
            FunctionDecl* Func = getOrCreateSubscriptFunction(E, Ctx);

            // Build call: func(&object, idx1, idx2, ...)
            std::vector&lt;Expr*&gt; Args;
            Args.push_back(Builder.addressOf(Object));
            Args.insert(Args.end(), Indices.begin(), Indices.end());

            // For lvalue context, return pointer dereference
            // For rvalue context, return value directly
            CallExpr* Call = Builder.callExpr(Func, Args);

            if (isLValueContext(E)) {
                return Builder.deref(Call);  // *func(...)
            } else {
                return Call;
            }
        }
        ```
      </code>
    </step>

    <step>
      <number>3</number>
      <description>Test Implementation</description>
      <code>
        ```cpp
        // In MultidimSubscriptTranslatorTest.cpp
        TEST(MultidimSubscriptTranslatorTest, Basic2DMatrix) {
            const char* code = R"(
                template&lt;typename T&gt;
                struct Matrix {
                    T& operator[](size_t row, size_t col) {
                        return data[row * cols + col];
                    }
                    T* data;
                    size_t rows, cols;
                };

                void test() {
                    Matrix&lt;int&gt; m;
                    m[1, 2] = 42;
                }
            )";

            auto C_Code = transpile(code);

            // Verify generated function exists
            EXPECT_THAT(C_Code, HasSubstr("Matrix_int__subscript"));

            // Verify function signature
            EXPECT_THAT(C_Code, HasSubstr(
                "int* Matrix_int__subscript(struct Matrix_int* self, "
                "size_t row, size_t col)"));

            // Verify call site transformation
            EXPECT_THAT(C_Code, HasSubstr(
                "*Matrix_int__subscript(&m, 1, 2) = 42"));
        }
        ```
      </code>
    </step>
  </implementation-details>

  <testing-strategy>
    1. Unit Tests (MultidimSubscriptTranslatorTest.cpp):
       - Basic 2D matrix access
       - 3D tensor access
       - Const vs non-const
       - Lvalue assignment: m[i,j] = value
       - Rvalue usage: x = m[i,j]
       - Chained subscript: m[i,j][k]

    2. Integration Tests (Phase 33 subset):
       - gcc-adapted/multidim-subscript-P2128/test01.cpp through test07.cpp
       - Expected pass rate: 14/16 tests (87%)

    3. A/B Testing:
       - Compile C++ version, run, capture output
       - Transpile to C, compile, run, capture output
       - Compare outputs for equivalence
  </testing-strategy>

  <risk-assessment>
    Low Risk:
    - Feature is syntactic sugar, no complex semantics
    - Clear transformation strategy
    - No interaction with other C++ features

    Potential Issues:
    - Call context detection (lvalue vs rvalue) may need refinement
    - Variadic subscript may require arity cap
    - Template instantiation timing (handle after monomorphization)

    Mitigation:
    - Start with non-template cases
    - Add template support after basic cases work
    - Use existing template infrastructure (TemplateExtractor)
  </risk-assessment>

  <success-criteria>
    - All 7 multidim-subscript-P2128 tests pass (Phase 33)
    - Unit test coverage ≥ 90%
    - No regressions (all existing tests still pass)
    - Code review approved
    - Documentation updated (FAQ.md entry)
  </success-criteria>
</phase>

### Phase 2: Static Operators (Weeks 3-4)

<phase>
  <id>2</id>
  <name>Static operator() and operator[] Support</name>
  <features>Feature #4: Static operator() and operator[] (P1169R4)</features>
  <estimated-effort>2 weeks</estimated-effort>
  <expected-improvement>+1-2% C++23 support (8 tests)</expected-improvement>

  <rationale>
    Build on Phase 1's operator handling knowledge. Static operators are
    simpler than multidim (no 'this' parameter) and validate the pattern
    of removing implicit parameters.
  </rationale>

  <dependencies>
    - Phase 1 complete (reuse operator detection patterns)
    - Existing: Static function transformation infrastructure
  </dependencies>

  <technical-approach>
    Week 1: Static operator() Detection and Transformation
    - Detect static operator() methods
    - Convert to static free functions
    - Transform call sites

    Week 2: Static operator[] and Integration
    - Add operator[] support
    - Combine with Phase 1's multidim handling
    - Handle static multidim subscript
    - Testing and validation
  </technical-approach>

  <files-to-create>
    include/StaticOperatorTranslator.h
    src/StaticOperatorTranslator.cpp
    tests/StaticOperatorTranslatorTest.cpp
  </files-to-create>

  <files-to-modify>
    include/CppToCVisitor.h (add handler for static operators)
    src/CppToCVisitor.cpp (route static operator calls)
    src/MultidimSubscriptTranslator.cpp (check for static qualifier)
  </files-to-modify>

  <implementation-details>
    <step>
      <number>1</number>
      <description>Detect Static Operators</description>
      <code>
        ```cpp
        // In CppToCVisitor::VisitCXXMethodDecl
        bool CppToCVisitor::VisitCXXMethodDecl(CXXMethodDecl* MD) {
            if (!MD->isStatic()) {
                // Existing logic for instance methods
                return true;
            }

            if (MD->isOverloadedOperator()) {
                auto Op = MD->getOverloadedOperator();
                if (Op == OO_Call || Op == OO_Subscript) {
                    // Handle static operator
                    auto C_Func = m_staticOperatorTrans->transform(MD, Context, C_TranslationUnit);
                    if (C_Func) {
                        C_TranslationUnit->addDecl(C_Func);
                    }
                }
            }

            return true;
        }
        ```
      </code>
    </step>

    <step>
      <number>2</number>
      <description>Transform to Static Function</description>
      <code>
        ```cpp
        // In StaticOperatorTranslator.cpp
        FunctionDecl* StaticOperatorTranslator::transform(
            CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU) {

            assert(MD->isStatic());

            // Generate name: Calculator__call_static or Calculator__subscript_static
            std::string FuncName = generateStaticOperatorName(MD);

            // Get return type and parameters (no 'this')
            QualType RetTy = MD->getReturnType();
            std::vector&lt;ParmVarDecl*&gt; Params;
            for (auto* Param : MD->parameters()) {
                Params.push_back(Param);  // Copy params as-is
            }

            // Create C function declaration
            FunctionDecl* C_Func = Builder.createFunction(
                FuncName, RetTy, Params, SC_Static);

            // Copy body if available
            if (MD->hasBody()) {
                Stmt* Body = MD->getBody();
                // Transform body (no 'this' substitution needed)
                Stmt* C_Body = transformStmt(Body);
                C_Func->setBody(C_Body);
            }

            return C_Func;
        }
        ```
      </code>
    </step>

    <step>
      <number>3</number>
      <description>Transform Call Sites</description>
      <code>
        ```cpp
        // In CppToCVisitor::VisitCXXOperatorCallExpr
        bool CppToCVisitor::VisitCXXOperatorCallExpr(CXXOperatorCallExpr* E) {
            auto* MethodDecl = dyn_cast_or_null&lt;CXXMethodDecl&gt;(E->getCalleeDecl());
            if (!MethodDecl) return true;

            if (MethodDecl->isStatic() &&
                (E->getOperator() == OO_Call || E->getOperator() == OO_Subscript)) {

                // Transform: obj.operator()(args) → Class__call_static(args)
                // Note: E->getArg(0) is the object (unused for static)

                std::vector&lt;Expr*&gt; Args;
                for (unsigned i = 1; i < E->getNumArgs(); ++i) {
                    Args.push_back(E->getArg(i));
                }

                FunctionDecl* StaticFunc = findStaticOperatorFunction(MethodDecl);
                CallExpr* C_Call = Builder.callExpr(StaticFunc, Args);

                // Replace E with C_Call in parent
                replaceExpr(E, C_Call);
            }

            return true;
        }
        ```
      </code>
    </step>
  </implementation-details>

  <testing-strategy>
    1. Unit Tests:
       - Static operator() with various signatures
       - Static operator[] single-arg
       - Static operator[] multi-arg (combined with Phase 1)
       - Call through instance vs. temporary

    2. Integration Tests:
       - tests/real-world/cpp23-validation/cpp/src/static_operators.cpp
       - Custom test cases for edge scenarios

    3. Validation:
       - Verify static functions have no 'this' parameter
       - Verify call sites omit object argument
       - A/B test for correctness
  </testing-strategy>

  <risk-assessment>
    Low Risk:
    - Simple transformation (remove implicit parameter)
    - No complex language semantics

    Potential Issues:
    - Call through instance may complicate detection
    - Combined with templates: ensure monomorphization happens first

    Mitigation:
    - Detect static qualifier early in visitor
    - Reuse template infrastructure from Phase 1
  </risk-assessment>

  <success-criteria>
    - static_operators.cpp test passes
    - Unit test coverage ≥ 85%
    - Combines correctly with multidim subscript
    - No regressions
  </success-criteria>
</phase>

### Phase 3: [[assume]] Attribute (Weeks 5-6)

<phase>
  <id>3</id>
  <name>[[assume]] Attribute Handling</name>
  <features>Feature #6: [[assume]] Attribute (P1774R8)</features>
  <estimated-effort>2 weeks</estimated-effort>
  <expected-improvement>+2% C++23 support (13 tests)</expected-improvement>

  <rationale>
    Low complexity, high test coverage. Provides experience with attribute
    handling before tackling more complex features. Can be implemented with
    multiple strategies (strip, comment, __builtin_assume).
  </rationale>

  <dependencies>
    - None (independent feature)
    - Existing: Attribute handling in AST visitor
  </dependencies>

  <technical-approach>
    Week 1: Attribute Detection and Stripping
    - Detect [[assume(condition)]] in AST
    - Implement stripping strategy with comment preservation
    - Handle expression translation for condition

    Week 2: Compiler Hint Conversion (Optional)
    - Add __builtin_assume() generation (GCC/Clang)
    - Add configuration flag: --assume-strategy={strip,comment,builtin}
    - Testing and documentation
  </technical-approach>

  <files-to-create>
    include/AssumeAttributeHandler.h
    src/AssumeAttributeHandler.cpp
    tests/AssumeAttributeHandlerTest.cpp
  </files-to-create>

  <files-to-modify>
    include/CppToCVisitor.h (add VisitAttributedStmt)
    src/CppToCVisitor.cpp (route assume attributes)
    include/CodeGenerator.h (add assume handling to emission)
  </files-to-modify>

  <implementation-details>
    <step>
      <number>1</number>
      <description>Detect Assume Attribute</description>
      <code>
        ```cpp
        // In CppToCVisitor.h
        bool VisitAttributedStmt(clang::AttributedStmt* S);
        std::unique_ptr&lt;AssumeAttributeHandler&gt; m_assumeHandler;

        // In CppToCVisitor.cpp
        bool CppToCVisitor::VisitAttributedStmt(AttributedStmt* S) {
            // Check for [[assume]] attribute
            for (const auto* Attr : S->getAttrs()) {
                if (auto* Assume = dyn_cast&lt;AssumeAttr&gt;(Attr)) {
                    m_assumeHandler->handle(S, Assume, Context, C_TranslationUnit);
                }
            }
            return true;
        }
        ```
      </code>
    </step>

    <step>
      <number>2</number>
      <description>Stripping Strategy</description>
      <code>
        ```cpp
        // In AssumeAttributeHandler.cpp
        void AssumeAttributeHandler::handle(AttributedStmt* S,
                                           AssumeAttr* Attr,
                                           ASTContext& Ctx,
                                           TranslationUnitDecl* C_TU) {

            // Get assumption condition
            Expr* Condition = Attr->getAssumption();

            // Translate condition to C (for comment or __builtin_assume)
            std::string CondStr;
            llvm::raw_string_ostream OS(CondStr);
            Condition->printPretty(OS, nullptr, PrintingPolicy(Ctx.getLangOpts()));
            OS.flush();

            // Strategy 1: Strip and comment
            if (strategy == AssumeStrategy::Comment) {
                // Emit: /* assume: condition */
                std::string Comment = "/* assume: " + CondStr + " */";
                // Attach comment to underlying statement
                attachComment(S->getSubStmt(), Comment);
            }

            // Strategy 2: Convert to __builtin_assume
            else if (strategy == AssumeStrategy::Builtin) {
                // Create: __builtin_assume(condition)
                auto* BuiltinCall = createBuiltinAssumeCall(Condition, Ctx);
                // Insert before underlying statement
                insertStmt(S->getSubStmt(), BuiltinCall);
            }

            // Strategy 3: Strip entirely
            else {
                // Just use underlying statement, discard attribute
            }

            // Always visit underlying statement
            // (attribute is metadata, doesn't affect semantics)
        }
        ```
      </code>
    </step>

    <step>
      <number>3</number>
      <description>Builtin Assume Generation</description>
      <code>
        ```cpp
        // In AssumeAttributeHandler.cpp
        CallExpr* AssumeAttributeHandler::createBuiltinAssumeCall(
            Expr* Condition, ASTContext& Ctx) {

            // Get __builtin_assume function
            // (This is a compiler builtin, doesn't need declaration)
            IdentifierInfo* II = &Ctx.Idents.get("__builtin_assume");

            // Create reference to builtin
            DeclarationName DN(II);
            DeclRefExpr* BuiltinRef = DeclRefExpr::Create(
                Ctx, NestedNameSpecifierLoc(), SourceLocation(),
                /*Decl=*/nullptr, /*RefersToEnclosingVariableOrCapture=*/false,
                DN, Ctx.VoidTy, VK_PRValue);

            // Create call: __builtin_assume(condition)
            Expr* Args[] = { Condition };
            CallExpr* Call = CallExpr::Create(
                Ctx, BuiltinRef, Args, Ctx.VoidTy,
                VK_PRValue, SourceLocation());

            return Call;
        }
        ```
      </code>
    </step>
  </implementation-details>

  <testing-strategy>
    1. Unit Tests:
       - Strip strategy: verify attribute removed
       - Comment strategy: verify comment present
       - Builtin strategy: verify __builtin_assume() call
       - Complex conditions: ensure C translation works

    2. Integration Tests:
       - tests/real-world/cpp23-validation/cpp/src/attributes.cpp
       - gcc-adapted tests (if available)

    3. Validation:
       - C code compiles cleanly
       - Runtime behavior unchanged (assume is hint only)
  </testing-strategy>

  <risk-assessment>
    Very Low Risk:
    - Attribute is optimization hint, doesn't affect semantics
    - Can safely strip if translation fails
    - No interaction with other features

    Potential Issues:
    - Complex C++ expressions in condition may not translate to C
    - Side effects in condition: must warn and strip

    Mitigation:
    - Fallback to strip strategy if condition translation fails
    - Detect side effects and warn user
  </risk-assessment>

  <success-criteria>
    - attributes.cpp test passes
    - Unit test coverage ≥ 95%
    - Documentation explains strategies
    - No regressions
  </success-criteria>
</phase>

### Phase 4: Deducing This (Weeks 7-10)

<phase>
  <id>4</id>
  <name>Deducing This (Explicit Object Parameters)</name>
  <features>Feature #1: Deducing This (P0847R7)</features>
  <estimated-effort>4 weeks</estimated-effort>
  <expected-improvement>+3-4% C++23 support (22 tests)</expected-improvement>

  <rationale>
    This is the most impactful C++23 language feature. Complex due to template
    deduction and overload generation, but follows established patterns from
    existing overload handling. Deferred to Phase 4 after building confidence
    with simpler features.
  </rationale>

  <dependencies>
    - Phases 1-3 complete (validation of workflow)
    - Existing: Template monomorphization, overload resolution
  </dependencies>

  <technical-approach>
    Week 1-2: Detection and Analysis
    - Detect explicit object parameters
    - Analyze template parameter constraints (auto, auto&, auto&&)
    - Design overload expansion strategy

    Week 3: Overload Generation
    - Generate 2-4 overloads based on qualifiers
    - Implement name mangling for each variant
    - Handle this-parameter substitution

    Week 4: Testing and Edge Cases
    - Recursive lambdas: extract to named functions
    - CRTP simplification
    - Comprehensive testing
  </technical-approach>

  <files-to-create>
    include/DeducingThisTranslator.h
    src/DeducingThisTranslator.cpp
    tests/DeducingThisTranslatorTest.cpp
  </files-to-create>

  <files-to-modify>
    include/CppToCVisitor.h (enhance VisitCXXMethodDecl)
    src/CppToCVisitor.cpp (route deducing-this methods)
    include/NameMangler.h (add cv-ref qualifier mangling)
    src/NameMangler.cpp (implement qualifier mangling)
  </files-to-modify>

  <implementation-details>
    <step>
      <number>1</number>
      <description>Detect Explicit Object Parameter</description>
      <code>
        ```cpp
        // In CppToCVisitor::VisitCXXMethodDecl
        bool CppToCVisitor::VisitCXXMethodDecl(CXXMethodDecl* MD) {
            // Check for explicit object parameter (C++23)
            if (MD->isExplicitObjectMemberFunction()) {
                auto C_Funcs = m_deducingThisTrans->transform(MD, Context, C_TranslationUnit);
                for (auto* C_Func : C_Funcs) {
                    C_TranslationUnit->addDecl(C_Func);
                }
                return true;
            }

            // Existing logic for regular methods
            // ...
        }
        ```
      </code>
    </step>

    <step>
      <number>2</number>
      <description>Analyze Parameter and Generate Overloads</description>
      <code>
        ```cpp
        // In DeducingThisTranslator.cpp
        std::vector&lt;FunctionDecl*&gt; DeducingThisTranslator::transform(
            CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU) {

            // Get explicit object parameter
            ParmVarDecl* ExplicitObjectParam = MD->getParamDecl(0);
            QualType ParamType = ExplicitObjectParam->getType();

            // Determine qualifiers to generate
            // Pattern: auto& → {T*, const T*}
            // Pattern: const auto& → {const T*}
            // Pattern: auto&& → {T*, const T*, T* (rvalue)}
            std::vector&lt;QualifierSet&gt; Overloads = determineOverloads(ParamType);

            std::vector&lt;FunctionDecl*&gt; C_Funcs;
            for (const auto& Quals : Overloads) {
                FunctionDecl* C_Func = generateOverload(MD, Quals, Ctx);
                C_Funcs.push_back(C_Func);
            }

            return C_Funcs;
        }

        std::vector&lt;QualifierSet&gt; DeducingThisTranslator::determineOverloads(
            QualType ParamType) {

            std::vector&lt;QualifierSet&gt; Result;

            // Check for auto, auto&, auto&&, const auto&
            if (ParamType->isLValueReferenceType()) {
                QualType Pointee = ParamType->getPointeeType();
                if (Pointee.isConstQualified()) {
                    // const auto& → const T* only
                    Result.push_back({true, false, false});  // const, lvalue
                } else {
                    // auto& → T* and const T*
                    Result.push_back({false, false, false}); // non-const, lvalue
                    Result.push_back({true, false, false});  // const, lvalue
                }
            } else if (ParamType->isRValueReferenceType()) {
                // auto&& → all combinations (forwarding reference)
                Result.push_back({false, false, false}); // T*, lvalue
                Result.push_back({true, false, false});  // const T*, lvalue
                Result.push_back({false, true, false});  // T*, rvalue
                Result.push_back({true, true, false});   // const T*, rvalue
            } else {
                // auto (by value) → single version
                Result.push_back({false, false, true});  // value
            }

            return Result;
        }
        ```
      </code>
    </step>

    <step>
      <number>3</number>
      <description>Generate Individual Overload</description>
      <code>
        ```cpp
        FunctionDecl* DeducingThisTranslator::generateOverload(
            CXXMethodDecl* MD, const QualifierSet& Quals, ASTContext& Ctx) {

            // Get class type
            CXXRecordDecl* Class = MD->getParent();

            // Generate mangled name with qualifiers
            // e.g., TextBuffer__get_lvalue, TextBuffer__get_const
            std::string FuncName = Mangler.mangleMethodWithQualifiers(
                Class, MD, Quals);

            // Build parameter list
            std::vector&lt;ParmVarDecl*&gt; Params;

            // First param: this pointer with appropriate qualifiers
            QualType ThisType;
            if (Quals.isValue) {
                // Pass by value: struct T
                ThisType = Ctx.getRecordType(Class);
            } else {
                // Pass by pointer: struct T* or const struct T*
                ThisType = Ctx.getPointerType(Ctx.getRecordType(Class));
                if (Quals.isConst) {
                    ThisType = Ctx.getConstType(ThisType);
                }
            }
            ParmVarDecl* ThisParam = Builder.createParam("self", ThisType);
            Params.push_back(ThisParam);

            // Remaining params: copy from original (skip explicit object param)
            for (unsigned i = 1; i < MD->getNumParams(); ++i) {
                Params.push_back(MD->getParamDecl(i));
            }

            // Create function
            QualType RetType = MD->getReturnType();
            FunctionDecl* C_Func = Builder.createFunction(
                FuncName, RetType, Params);

            // Transform body: substitute explicit object param with 'self'
            if (MD->hasBody()) {
                Stmt* Body = MD->getBody();
                Stmt* C_Body = substituteExplicitObjectParam(
                    Body, MD->getParamDecl(0), ThisParam);
                C_Func->setBody(C_Body);
            }

            return C_Func;
        }
        ```
      </code>
    </step>

    <step>
      <number>4</number>
      <description>Transform Call Sites</description>
      <code>
        ```cpp
        // In CppToCVisitor.cpp or DeducingThisTranslator.cpp
        // Override expression transformation to handle calls to deducing-this methods

        Expr* transformDeducingThisCall(CXXMemberCallExpr* Call, ASTContext& Ctx) {
            CXXMethodDecl* Method = Call->getMethodDecl();
            if (!Method->isExplicitObjectMemberFunction()) {
                return Call;  // Not deducing-this
            }

            // Get object expression
            Expr* Object = Call->getImplicitObjectArgument();

            // Determine qualifiers of object at call site
            QualifierSet CallQuals = analyzeCallSiteQualifiers(Object);

            // Find matching overload
            FunctionDecl* Overload = findMatchingOverload(Method, CallQuals);

            // Build call: func(&object, args...)
            std::vector&lt;Expr*&gt; Args;
            Args.push_back(Builder.addressOf(Object));
            for (auto* Arg : Call->arguments()) {
                Args.push_back(Arg);
            }

            CallExpr* C_Call = Builder.callExpr(Overload, Args);
            return C_Call;
        }

        QualifierSet DeducingThisTranslator::analyzeCallSiteQualifiers(Expr* Object) {
            QualType ObjType = Object->getType();

            QualifierSet Quals;
            Quals.isConst = ObjType.isConstQualified();
            Quals.isRValue = Object->isRValue();
            Quals.isValue = false;

            return Quals;
        }
        ```
      </code>
    </step>
  </implementation-details>

  <testing-strategy>
    1. Unit Tests:
       - auto& parameter → 2 overloads
       - const auto& parameter → 1 overload
       - auto&& parameter → 4 overloads
       - auto parameter → 1 overload (by value)
       - Call site qualifier matching
       - Recursive lambda extraction

    2. Integration Tests:
       - tests/real-world/cpp23-validation/cpp/src/deducing_this.cpp
       - All 7 test scenarios from test file

    3. A/B Testing:
       - Verify lvalue calls use lvalue overload
       - Verify const calls use const overload
       - Verify rvalue calls use rvalue overload
  </testing-strategy>

  <risk-assessment>
    Medium-High Risk:
    - Complex feature with template deduction
    - Multiple overloads increase code size
    - Call site analysis may be fragile

    Potential Issues:
    - Recursive lambdas: requires lambda-to-function extraction
    - CRTP: may interact with template monomorphization
    - Overload ambiguity: need clear selection rules
    - Rvalue semantics in C: limited support

    Mitigation:
    - Start with simple cases (auto&, const auto&)
    - Add forwarding reference (auto&&) after basics work
    - Reuse lambda extraction if available, or implement simplified version
    - Extensive testing with different call patterns
  </risk-assessment>

  <success-criteria>
    - deducing_this.cpp test passes (≥6/7 scenarios)
    - Unit test coverage ≥ 80%
    - Overload selection is deterministic and correct
    - No regressions
    - Documentation explains transformation
  </success-criteria>
</phase>

### Phase 5: if consteval (Weeks 11-13)

<phase>
  <id>5</id>
  <name>if consteval Support</name>
  <features>Feature #2: if consteval (P1938R3)</features>
  <estimated-effort>3 weeks</estimated-effort>
  <expected-improvement>+2% C++23 support (13 tests)</expected-improvement>

  <rationale>
    Complex feature requiring compile-time evaluation. Deferred after
    building experience with attribute handling (Phase 3) and complex
    transformations (Phase 4). May provide limited support (runtime fallback)
    if full compile-time evaluation proves too complex.
  </rationale>

  <dependencies>
    - Phases 1-4 complete
    - Existing: Clang constant evaluator (may need to invoke)
  </dependencies>

  <technical-approach>
    Week 1: Detection and Context Analysis
    - Detect if consteval statements
    - Analyze usage context (constexpr function, constant expression)
    - Determine which branch to emit

    Week 2: Branch Selection and Emission
    - Implement compile-time evaluation for simple cases
    - Emit appropriate branch based on context
    - Handle runtime fallback

    Week 3: Advanced Cases and Testing
    - Handle nested if consteval
    - Handle if !consteval
    - Comprehensive testing
  </technical-approach>

  <files-to-create>
    include/ConstevalIfTranslator.h
    src/ConstevalIfTranslator.cpp
    tests/ConstevalIfTranslatorTest.cpp
  </files-to-create>

  <files-to-modify>
    include/CppToCVisitor.h (add VisitIfStmt enhancement or new visitor)
    src/CppToCVisitor.cpp (route consteval-if statements)
  </files-to-modify>

  <implementation-details>
    <step>
      <number>1</number>
      <description>Detect if consteval</description>
      <code>
        ```cpp
        // In CppToCVisitor::VisitIfStmt
        bool CppToCVisitor::VisitIfStmt(IfStmt* S) {
            // Check if this is 'if consteval'
            if (S->isConsteval()) {
                auto C_Stmt = m_constevalIfTrans->transform(S, Context, C_TranslationUnit);
                if (C_Stmt) {
                    replaceStmt(S, C_Stmt);
                }
                return true;
            }

            // Regular if statement
            // ...
        }
        ```
      </code>
    </step>

    <step>
      <number>2</number>
      <description>Analyze Context and Select Branch</description>
      <code>
        ```cpp
        // In ConstevalIfTranslator.cpp
        Stmt* ConstevalIfTranslator::transform(
            IfStmt* S, ASTContext& Ctx, TranslationUnitDecl* C_TU) {

            // Determine if we're in a constexpr context
            bool IsConstexprContext = analyzeContext(S, Ctx);

            // Get branches
            Stmt* ThenBranch = S->getThen();    // consteval path
            Stmt* ElseBranch = S->getElse();    // runtime path

            // Check for negated form: if !consteval
            bool IsNegated = S->isNegatedConsteval();
            if (IsNegated) {
                std::swap(ThenBranch, ElseBranch);
            }

            // Select branch based on context
            Stmt* SelectedBranch = nullptr;
            if (IsConstexprContext) {
                // Emit consteval (then) branch
                SelectedBranch = ThenBranch;
                emitWarning("if consteval: using compile-time path");
            } else {
                // Emit runtime (else) branch
                SelectedBranch = ElseBranch;
                emitWarning("if consteval: using runtime path (C has no consteval)");
            }

            // Transform selected branch
            return transformStmt(SelectedBranch);
        }

        bool ConstevalIfTranslator::analyzeContext(IfStmt* S, ASTContext& Ctx) {
            // Walk up AST to find enclosing function
            FunctionDecl* EnclosingFunc = findEnclosingFunction(S, Ctx);
            if (!EnclosingFunc) {
                return false;  // Not in function → runtime
            }

            // Check if function is constexpr
            if (!EnclosingFunc->isConstexpr()) {
                return false;  // Non-constexpr function → runtime
            }

            // Check if this call site is constant-evaluated
            // (This requires whole-program analysis or conservative approximation)
            // For now, use heuristics:
            // - If function is called with constexpr args → compile-time
            // - If result assigned to constexpr var → compile-time
            // - Otherwise → runtime

            // Conservative approach: default to runtime unless we can prove compile-time
            return isDefinitelyConstexprContext(S, EnclosingFunc, Ctx);
        }
        ```
      </code>
    </step>

    <step>
      <number>3</number>
      <description>Macro-Based Strategy (Alternative)</description>
      <code>
        ```cpp
        // Alternative approach: Generate both paths with macro selection

        Stmt* ConstevalIfTranslator::transformToMacro(
            IfStmt* S, ASTContext& Ctx, TranslationUnitDecl* C_TU) {

            // Strategy: Use C preprocessor for compile-time path
            // Generate:
            //   #ifdef __cplusplus_consteval_available
            //     /* consteval path */
            //   #else
            //     /* runtime path */
            //   #endif

            // This approach preserves both paths but requires C99 macros

            std::string MacroCode = generateMacroGuardedCode(S, Ctx);

            // Attach as comment or auxiliary code
            // (Requires CodeGenerator enhancement to emit preprocessor directives)

            return S;  // Keep original structure, add macro guards during emission
        }
        ```
      </code>
    </step>
  </implementation-details>

  <testing-strategy>
    1. Unit Tests:
       - if consteval in constexpr function
       - if consteval in regular function
       - if !consteval (negated form)
       - Nested if consteval
       - Branch selection correctness

    2. Integration Tests:
       - tests/real-world/cpp23-validation/cpp/src/consteval_if.cpp
       - All 6 test scenarios

    3. Validation:
       - Runtime path produces correct results
       - Warning emitted when compile-time optimization lost
  </testing-strategy>

  <risk-assessment>
    High Risk:
    - Requires compile-time context analysis
    - May lose compile-time optimizations
    - Whole-program analysis challenging

    Potential Issues:
    - Determining constexpr context is non-trivial
    - False negatives: emit runtime path when compile-time possible
    - Complex consteval code may not translate to C

    Mitigation:
    - Start with conservative approach (default to runtime)
    - Emit clear warnings when optimization lost
    - Provide configuration option: --consteval-strategy={runtime,macro,error}
    - Accept partial support (runtime fallback) as valid outcome
  </risk-assessment>

  <success-criteria>
    - consteval_if.cpp test passes with runtime fallback
    - Unit test coverage ≥ 75%
    - Clear warnings emitted for optimization loss
    - Documentation explains limitation
    - No regressions
  </success-criteria>
</phase>

### Phase 6: Partial Constexpr and auto(x) (Weeks 14-16)

<phase>
  <id>6</id>
  <name>Partial Constexpr Enhancements and auto(x) Decay-Copy</name>
  <features>
    Feature #7: Constexpr Enhancements (partial)
    Feature #5: auto(x) and auto{x} Decay-Copy (P0849R8)
  </features>
  <estimated-effort>3 weeks</estimated-effort>
  <expected-improvement>+4-5% C++23 support (combined: ~20 tests)</expected-improvement>

  <rationale>
    Final phase focuses on lower-priority features with partial support.
    Constexpr enhancements have high complexity, so we target simple cases
    (compile-time literals) and runtime fallback. auto(x) is medium complexity
    with clear transformation rules.
  </rationale>

  <dependencies>
    - All previous phases complete
    - Existing: Template type deduction infrastructure
  </dependencies>

  <technical-approach>
    Week 1: auto(x) Decay-Copy
    - Detect auto(x) and auto{x} expressions
    - Implement type decay rules
    - Generate explicit copy code

    Week 2: Simple Constexpr Evaluation
    - Detect constexpr functions with C++23 features
    - Attempt compile-time evaluation for literals
    - Emit constants or runtime fallback

    Week 3: Integration and Testing
    - Combine both features
    - Comprehensive testing
    - Documentation
  </technical-approach>

  <files-to-create>
    include/AutoDecayCopyTranslator.h
    src/AutoDecayCopyTranslator.cpp
    tests/AutoDecayCopyTranslatorTest.cpp
    include/ConstexprEnhancementHandler.h (optional, may reuse existing)
    src/ConstexprEnhancementHandler.cpp
    tests/ConstexprEnhancementTest.cpp
  </files-to-create>

  <files-to-modify>
    include/CppToCVisitor.h (add visitors for functional casts, constexpr funcs)
    src/CppToCVisitor.cpp (route to handlers)
  </files-to-modify>

  <implementation-details>
    <step>
      <number>1</number>
      <description>Detect auto(x) Decay-Copy</description>
      <code>
        ```cpp
        // In CppToCVisitor::VisitCXXFunctionalCastExpr
        bool CppToCVisitor::VisitCXXFunctionalCastExpr(CXXFunctionalCastExpr* E) {
            // Check if this is auto(x) or auto{x}
            if (auto* AutoType = dyn_cast&lt;AutoType&gt;(E->getTypeAsWritten().getTypePtr())) {
                auto C_Expr = m_autoDecayTrans->transform(E, Context);
                if (C_Expr) {
                    replaceExpr(E, C_Expr);
                }
                return true;
            }

            // Regular cast
            // ...
        }
        ```
      </code>
    </step>

    <step>
      <number>2</number>
      <description>Implement Decay-Copy Transformation</description>
      <code>
        ```cpp
        // In AutoDecayCopyTranslator.cpp
        Expr* AutoDecayCopyTranslator::transform(
            CXXFunctionalCastExpr* E, ASTContext& Ctx) {

            // Get source expression
            Expr* Source = E->getSubExpr();
            QualType SourceType = Source->getType();

            // Compute decayed type
            QualType DecayedType = computeDecayedType(SourceType, Ctx);

            // Generate copy expression based on type
            if (SourceType->isReferenceType()) {
                // Reference → value: dereference
                // E.g., const int& → int copy
                return Builder.deref(Source);
            } else if (SourceType->isArrayType()) {
                // Array → pointer: implicit decay
                return Source;  // C naturally decays arrays
            } else if (SourceType->isFunctionType()) {
                // Function → function pointer: address-of
                return Builder.addressOf(Source);
            } else {
                // Value type: explicit copy
                // For class types, invoke copy constructor
                if (auto* RecordType = SourceType->getAsCXXRecordDecl()) {
                    return generateCopyConstructorCall(Source, RecordType, Ctx);
                } else {
                    // Primitive: simple assignment suffices
                    return Source;
                }
            }
        }

        QualType AutoDecayCopyTranslator::computeDecayedType(
            QualType Ty, ASTContext& Ctx) {

            // Remove references
            if (Ty->isReferenceType()) {
                Ty = Ty.getNonReferenceType();
            }

            // Remove cv-qualifiers
            Ty = Ty.getUnqualifiedType();

            // Array-to-pointer decay
            if (const auto* ArrTy = Ctx.getAsArrayType(Ty)) {
                Ty = Ctx.getPointerType(ArrTy->getElementType());
            }

            // Function-to-pointer decay
            if (Ty->isFunctionType()) {
                Ty = Ctx.getPointerType(Ty);
            }

            return Ty;
        }
        ```
      </code>
    </step>

    <step>
      <number>3</number>
      <description>Constexpr Enhancement (Simple Cases)</description>
      <code>
        ```cpp
        // In ConstexprEnhancementHandler.cpp
        // Handle constexpr functions that use C++23 features

        void ConstexprEnhancementHandler::handleConstexprFunction(
            FunctionDecl* FD, ASTContext& Ctx, TranslationUnitDecl* C_TU) {

            if (!FD->isConstexpr()) return;

            // Check if function uses C++23 constexpr features
            bool UsesC23Features = detectC23ConstexprFeatures(FD);
            if (!UsesC23Features) return;

            // Try to evaluate function at compile-time using Clang evaluator
            Expr::EvalResult Result;
            if (attemptCompileTimeEval(FD, Result, Ctx)) {
                // Success: emit constant
                emitConstant(FD, Result, C_TU);
            } else {
                // Fallback: emit as runtime function
                emitWarning(FD, "Constexpr function with C++23 features "
                           "cannot be evaluated at compile-time; "
                           "emitting as runtime function");
                emitRuntimeFunction(FD, Ctx, C_TU);
            }
        }

        bool ConstexprEnhancementHandler::attemptCompileTimeEval(
            FunctionDecl* FD, Expr::EvalResult& Result, ASTContext& Ctx) {

            // Simple heuristic: only try if function body is simple
            if (!FD->hasBody()) return false;

            Stmt* Body = FD->getBody();

            // Use Clang's constant evaluator
            // (This is complex; may require constructing call expression)

            // For very simple cases: if body is 'return literal;'
            if (auto* RS = dyn_cast&lt;ReturnStmt&gt;(Body)) {
                if (Expr* RetVal = RS->getRetValue()) {
                    return RetVal->EvaluateAsRValue(Result, Ctx);
                }
            }

            return false;
        }
        ```
      </code>
    </step>
  </implementation-details>

  <testing-strategy>
    1. Unit Tests:
       - auto(x) with reference types
       - auto(x) with array types
       - auto(x) with function types
       - auto(x) with class types
       - auto{x} (braced-init variant)
       - Simple constexpr evaluation
       - Constexpr runtime fallback

    2. Integration Tests:
       - Subset of gcc-adapted/constexpr-enhancements tests (simple cases)
       - Custom tests for auto(x)

    3. Validation:
       - Decay semantics match C++ behavior
       - Constexpr literals correctly evaluated
  </testing-strategy>

  <risk-assessment>
    Medium Risk:
    - auto(x) is straightforward but requires correct type analysis
    - Constexpr evaluation is complex, high chance of runtime fallback

    Potential Issues:
    - Class copy constructors may not be available
    - Constexpr evaluation engine may fail frequently
    - Complex constexpr code: not supported

    Mitigation:
    - Focus on simple, common cases
    - Accept runtime fallback as valid outcome
    - Clear documentation of limitations
  </risk-assessment>

  <success-criteria>
    - auto(x) tests pass (≥80%)
    - Constexpr simple cases pass (≥40%, runtime fallback acceptable)
    - Unit test coverage ≥ 75%
    - Documentation explains partial support
    - Overall C++23 support reaches 20-25%
    - No regressions
  </success-criteria>
</phase>

---

## Timeline Summary

| Phase | Duration | Features | Tests | Cumulative % |
|-------|----------|----------|-------|--------------|
| 0 (Baseline) | - | - | 0 | 0.0% |
| 1 | Weeks 1-2 | Multidim subscript | 16 | 3-4% |
| 2 | Weeks 3-4 | Static operators | 8 | 5-6% |
| 3 | Weeks 5-6 | [[assume]] | 13 | 7-8% |
| 4 | Weeks 7-10 | Deducing this | 22 | 10-12% |
| 5 | Weeks 11-13 | if consteval | 13 | 12-14% |
| 6 | Weeks 14-16 | Partial constexpr + auto(x) | ~20 | **20-25%** |

**Total timeline**: 16 weeks (4 months)

---

## Success Metrics

### Overall Goals
- C++23 support: **0% → 20-25%**
- Test pass rate: **0/~150 → 30-40/~150**
- No regressions: All existing tests still pass
- Code quality: 80%+ coverage on new code
- Build time impact: <15% increase

### Per-Phase Gates
Each phase must meet these criteria before proceeding:
1. **Functionality**: Feature works for documented use cases
2. **Testing**: Unit tests ≥75% coverage, integration tests pass
3. **Quality**: Code review approved, no critical bugs
4. **Documentation**: README/FAQ updated with feature support
5. **Stability**: No regressions in existing test suite

### Quality Metrics
- **Code coverage**: 80%+ on new transformation code
- **Compilation**: Generated C code compiles without warnings (C99 + -Wall)
- **Correctness**: A/B testing shows matching behavior
- **Performance**: Transpilation time increase <20% per phase

---

## Risk Management

### High-Level Risks

<risk>
  <level>High</level>
  <description>Deducing This (Phase 4) complexity higher than estimated</description>
  <probability>Medium (40%)</probability>
  <impact>Schedule delay of 1-2 weeks</impact>
  <mitigation>
    - Budget 4 weeks instead of 3
    - Implement minimal support (auto& only) if full support blocked
    - Move complex cases (recursive lambdas, CRTP) to future phase
  </mitigation>
</risk>

<risk>
  <level>High</level>
  <description>if consteval (Phase 5) may not be fully implementable</description>
  <probability>High (60%)</probability>
  <impact>Reduced feature coverage (runtime fallback only)</impact>
  <mitigation>
    - Accept runtime fallback as valid outcome
    - Document limitation clearly
    - Provide configuration flag for strategy selection
    - De-scope if necessary (move to future)
  </mitigation>
</risk>

<risk>
  <level>Medium</level>
  <description>Header file skipping blocks some test coverage</description>
  <probability>High (70%)</probability>
  <impact>Tests still fail despite correct transformation</impact>
  <mitigation>
    - Move test code from headers to .cpp files where possible
    - Document header limitation in Phase 33 report
    - Consider header transformation as separate project (out of scope)
  </mitigation>
</risk>

<risk>
  <level>Medium</level>
  <description>Template interaction with C++23 features</description>
  <probability>Medium (50%)</probability>
  <impact>Template + C++23 combinations fail</impact>
  <mitigation>
    - Ensure monomorphization happens before C++23 transformation
    - Test template cases explicitly
    - May need to enhance TemplateMonomorphizer
  </mitigation>
</risk>

<risk>
  <level>Low</level>
  <description>CNodeBuilder insufficient for new C patterns</description>
  <probability>Low (20%)</probability>
  <impact>Need to extend CNodeBuilder API</impact>
  <mitigation>
    - Review CNodeBuilder early in Phase 1
    - Add helpers as needed (follows existing pattern)
    - Low complexity - well-understood problem
  </mitigation>
</risk>

### Risk Response Strategy
- **Weekly check-ins**: Assess progress vs. plan
- **Adjust scope**: If phase exceeds timeline, reduce to minimal viable feature
- **Defer complex cases**: Move edge cases to "future work" if blocking
- **Document limitations**: Clear communication about partial support

---

## Architecture Integration

### Visitor Pattern Integration

The RecursiveASTVisitor pattern in CppToCVisitor supports incremental feature addition:

```
CppToCVisitor (coordinator)
  ├─ VisitCXXRecordDecl → Struct generation
  ├─ VisitCXXMethodDecl → Method transformation
  │    └─ Check for explicit object param → DeducingThisTranslator
  │    └─ Check for static operator → StaticOperatorTranslator
  ├─ VisitCXXOperatorCallExpr → Operator transformations
  │    └─ Check for multidim subscript → MultidimSubscriptTranslator
  ├─ VisitAttributedStmt → Attribute handling
  │    └─ Check for [[assume]] → AssumeAttributeHandler
  ├─ VisitIfStmt → Statement transformation
  │    └─ Check for consteval → ConstevalIfTranslator
  └─ VisitCXXFunctionalCastExpr → Expression transformation
       └─ Check for auto(x) → AutoDecayCopyTranslator
```

### CNodeBuilder Extensions

May need new helpers:
```cpp
// Potential additions to CNodeBuilder
Expr* deref(Expr* ptr);                    // *ptr
Expr* addressOf(Expr* val);                // &val
CallExpr* callExpr(FunctionDecl* func,
                   ArrayRef<Expr*> args);  // func(args...)
ParmVarDecl* createParam(StringRef name,
                         QualType type);    // Parameter creation
```

### C AST Node Types Needed

All required node types already exist in Clang's C AST:
- `FunctionDecl` - for generated C functions
- `RecordDecl` - for structs (already used)
- `ParmVarDecl` - for function parameters
- `CallExpr` - for function calls
- `DeclRefExpr` - for variable references
- `UnaryOperator` - for *, &, etc.
- `CompoundStmt` - for { } blocks
- `ReturnStmt` - for return statements
- `IfStmt` - for if statements (non-consteval)
- `WhileStmt`, `ForStmt` - for loops

No new C AST node types required - all transformations map to existing C constructs.

---

## Testing Strategy

### Test Pyramid

```
                  ┌─────────────────┐
                  │  A/B Testing    │  ← Behavioral equivalence
                  │  (5-10 tests)   │
                  └─────────────────┘
                         ▲
                ┌────────┴────────┐
                │  Integration    │  ← Phase 33 tests
                │  (30-40 tests)  │
                └─────────────────┘
                         ▲
              ┌──────────┴──────────┐
              │    Unit Tests       │  ← Feature coverage
              │  (100-150 tests)    │
              └─────────────────────┘
```

### Unit Testing Approach

Each translator has dedicated test file:
```cpp
// Example: MultidimSubscriptTranslatorTest.cpp

TEST(MultidimSubscriptTranslatorTest, Basic2D) {
    // Test basic 2D subscript transformation
}

TEST(MultidimSubscriptTranslatorTest, ConstOverload) {
    // Test const version
}

TEST(MultidimSubscriptTranslatorTest, LValueAssignment) {
    // Test assignment context
}

// ... 10-15 tests per feature
```

### Integration Testing (Phase 33)

Leverage existing Phase 33 test infrastructure:
```
tests/real-world/cpp23-validation/
  ├─ gcc-adapted/multidim-subscript-P2128/  (16 tests) → Phase 1
  ├─ gcc-adapted/constexpr-enhancements/    (19 tests) → Phase 6
  ├─ cpp/src/deducing_this.cpp              (7 scenarios) → Phase 4
  ├─ cpp/src/consteval_if.cpp               (6 scenarios) → Phase 5
  ├─ cpp/src/static_operators.cpp           (3 scenarios) → Phase 2
  └─ cpp/src/attributes.cpp                 (assume tests) → Phase 3
```

### A/B Testing Methodology

For each test case:
1. **Compile C++**: `clang++ -std=c++23 test.cpp -o test_cpp`
2. **Run C++**: `./test_cpp > cpp_output.txt`
3. **Transpile**: `cpptoc test.cpp -o test.c`
4. **Compile C**: `gcc -std=c99 test.c -o test_c`
5. **Run C**: `./test_c > c_output.txt`
6. **Compare**: `diff cpp_output.txt c_output.txt`

### Regression Testing

Before each commit:
```bash
# Run all existing tests
cd build_working
ctest --output-on-failure

# Verify no regressions
scripts/run-all-tests.sh
```

Regression criteria:
- All pre-existing tests must still pass
- No new compiler warnings
- Build time increase < 10% per phase

---

## Documentation Requirements

### Per-Phase Deliverables

Each phase must update:

1. **README.md**:
   - Add feature to "Supported C++23 Features" section
   - Example code snippet showing transformation

2. **FAQ.md**:
   - Add entry explaining feature support level
   - Document known limitations
   - Provide workarounds if applicable

3. **TESTING.md**:
   - Document new test files
   - Explain test coverage strategy
   - Update test count metrics

4. **Code Documentation**:
   - Doxygen comments for all public APIs
   - Inline comments explaining complex logic
   - Transformation examples in header comments

### Final Documentation (End of Phase 6)

Create comprehensive C++23 support document:

**docs/CPP23_SUPPORT.md**:
```markdown
# C++23 Feature Support in cpptoc

## Fully Supported Features
- Multidimensional subscript operator (P2128R6)
- Static operator() and operator[] (P1169R4)
- [[assume]] attribute (P1774R8) - stripped with comment

## Partially Supported Features
- Deducing this (P0847R7) - lvalue/const variants only
- if consteval (P1938R3) - runtime fallback
- auto(x) decay-copy (P0849R8) - common cases
- Constexpr enhancements - simple cases only

## Not Supported
- [List unsupported C++23 features]

## Examples
[Detailed examples for each feature]

## Limitations
[Detailed explanation of partial support]
```

---

## Deferred Features

The following C++23 features are **out of scope** for this plan but could be addressed in future work:

### Library Features (Not Language Features)
- `std::print` / `std::println` (P2093R14) - requires runtime library
- `std::expected` (P0323R12) - complex type, needs full monomorphization
- `std::flat_map` / `std::flat_set` (P0429R9) - STL containers
- Ranges enhancements - STL library

### Complex Language Features
- Pattern matching (P2688R0) - if included in final C++23 - highly complex
- Literal suffix for `size_t` (P0330R8) - low impact
- Multidimensional array subscripting for built-in arrays - edge case

### Rationale for Deferral
These features either:
1. Require extensive runtime library support (std::print, std::expected)
2. Are extremely complex (pattern matching)
3. Have minimal real-world impact (literal suffixes)
4. Duplicate existing capabilities (ranges)

The goal is to maximize C++23 **language feature** support with reasonable effort, not achieve 100% C++23 compatibility.

---

## Implementation Checklist

Before starting Phase 1, verify:
- [ ] Build environment ready (CMake, Clang 18+, GCC/Clang C99)
- [ ] Test infrastructure working (ctest, run-all-tests.sh)
- [ ] Git flow configured
- [ ] Phase 33 baseline established (0.0% C++23 support documented)
- [ ] Team aligned on priorities and timeline

Per-phase checklist:
- [ ] Create feature branch: `feature/phase-N-{feature-name}`
- [ ] Implement transformation logic
- [ ] Write unit tests (≥75% coverage)
- [ ] Run integration tests (Phase 33 subset)
- [ ] Perform A/B testing (sample tests)
- [ ] Update documentation (README, FAQ, code comments)
- [ ] Code review
- [ ] Merge to develop
- [ ] Tag release: `v{version}-phase-{N}`

Final checklist (after Phase 6):
- [ ] All 6 phases complete
- [ ] C++23 support ≥ 20%
- [ ] No regressions
- [ ] Full documentation updated
- [ ] Release notes prepared
- [ ] Git release: `v3.0.0-cpp23-support`

---

## Conclusion

This implementation plan provides a **systematic, incremental roadmap** to add C++23 feature support to the cpptoc transpiler, targeting **20-25% C++23 coverage** over **16 weeks** through **6 focused phases**.

### Key Success Factors

1. **Incremental approach**: Each phase is independently valuable and testable
2. **Risk management**: Complex features deferred until experience gained
3. **Clear validation**: Unit tests, integration tests, A/B testing at each phase
4. **Realistic scope**: Accepts partial support and runtime fallbacks where appropriate
5. **Proven patterns**: Follows existing visitor/translator architecture

### Expected Outcomes

By the end of Phase 6:
- **8 C++23 features** with full or partial support
- **30-40 Phase 33 tests** passing (20-25% support)
- **100-150 new unit tests** providing thorough coverage
- **Zero regressions** in existing functionality
- **Comprehensive documentation** of capabilities and limitations

### Next Step

**Begin Phase 1 immediately**: Multidimensional Subscript Operator support is well-scoped, low-risk, and validates the entire workflow. Success in Phase 1 will build confidence and momentum for subsequent phases.
