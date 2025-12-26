# Handler Testing Strategy

## Overview

The handler-based architecture enables **surgical unit testing** where each handler can be tested independently without running the entire transpilation pipeline.

## Testing Pyramid

```
         ┌─────────────────┐
         │  Integration    │  5-10 tests per phase
         │     Tests       │  (End-to-end: C++ → C)
         └─────────────────┘
               ▲
        ┌──────┴──────┐
        │   Handler   │       20-30 tests per handler
        │  Integration│       (Multi-handler scenarios)
        └─────────────┘
              ▲
       ┌──────┴───────┐
       │    Handler   │        50+ tests per handler
       │  Unit Tests  │        (Isolated C++ AST → C AST)
       └──────────────┘
```

---

## Unit Testing: Individual Handlers

### Objective
Test each handler in **complete isolation** - verify it creates correct C AST nodes from C++ AST nodes.

### Test Structure

```cpp
// Example: FunctionHandler unit test
TEST(FunctionHandlerTest, SimpleFunctionDeclaration) {
    // 1. ARRANGE: Create mock C++ AST
    ASTContext cppCtx = createMockCppContext();
    FunctionDecl* cppFunc = createMockFunction(
        cppCtx,
        "int",           // return type
        "add",           // name
        {"int a", "int b"}  // parameters
    );

    // Create C AST context and handler
    ASTContext cCtx = createMockCContext();
    CNodeBuilder builder(cCtx);
    HandlerContext context(cppCtx, cCtx, builder);
    FunctionHandler handler;

    // 2. ACT: Translate
    Decl* result = handler.handleDecl(cppFunc, context);

    // 3. ASSERT: Verify C AST
    ASSERT_NE(result, nullptr);
    FunctionDecl* cFunc = dyn_cast<FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    // Check function name
    EXPECT_EQ(cFunc->getNameAsString(), "add");

    // Check return type
    EXPECT_TRUE(cFunc->getReturnType()->isIntegerType());

    // Check parameters
    ASSERT_EQ(cFunc->getNumParams(), 2);
    EXPECT_EQ(cFunc->getParamDecl(0)->getNameAsString(), "a");
    EXPECT_EQ(cFunc->getParamDecl(1)->getNameAsString(), "b");

    // Verify NO code was generated (that's Stage 3's job)
    // We only check AST structure
}
```

### Key Principles

1. **No Code Emission**: Unit tests verify AST structure, NOT generated text
2. **Mock C++ AST**: Create minimal C++ AST nodes for testing
3. **Inspect C AST**: Use AST matchers and assertions to verify structure
4. **Isolated**: Each test runs one handler with mocked dependencies

### Test Utilities

```cpp
// Test helper: Create mock AST contexts
class MockASTHelper {
public:
    static ASTContext createCppContext();
    static ASTContext createCContext();

    static FunctionDecl* createFunction(
        ASTContext& ctx,
        const std::string& returnType,
        const std::string& name,
        const std::vector<std::string>& params
    );

    static CXXRecordDecl* createClass(
        ASTContext& ctx,
        const std::string& name,
        const std::vector<std::string>& fields
    );

    // ... more helpers
};
```

### AST Matchers

Use Clang's AST matchers for verification:

```cpp
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"

using namespace clang::ast_matchers;

TEST(ExpressionHandlerTest, BinaryAddition) {
    // ... create BinaryOperator for "a + b"

    Expr* result = handler.handleExpr(cppExpr, context);

    // Match: BinaryOperator with operator '+'
    auto matcher = binaryOperator(
        hasOperatorName("+"),
        hasLHS(declRefExpr(to(varDecl(hasName("a"))))),
        hasRHS(declRefExpr(to(varDecl(hasName("b")))))
    );

    EXPECT_TRUE(match(matcher, *result, cCtx));
}
```

---

## Handler Integration Testing

### Objective
Test **multiple handlers working together** for complex scenarios (e.g., class with methods requires RecordHandler + MethodHandler).

### Test Structure

```cpp
TEST(ClassTranslationTest, ClassWithMethod) {
    // 1. ARRANGE: Create full C++ class AST
    /*
        class Counter {
            int count;
        public:
            void increment() { count++; }
        };
    */

    ASTContext cppCtx = createMockCppContext();
    CXXRecordDecl* cppClass = createMockClass(cppCtx, "Counter");
    addField(cppClass, "int", "count", AccessSpecifier::AS_private);
    CXXMethodDecl* method = addMethod(cppClass, "void", "increment", {});
    addMethodBody(method, "count++");

    // Create translation infrastructure
    ASTContext cCtx = createMockCContext();
    CNodeBuilder builder(cCtx);
    HandlerContext context(cppCtx, cCtx, builder);

    // Create orchestrator with all handlers
    HandlerRegistry registry;
    registry.registerHandler(new RecordHandler());
    registry.registerHandler(new MethodHandler());
    registry.registerHandler(new ExpressionHandler());
    registry.registerHandler(new StatementHandler());

    TranslationOrchestrator orchestrator(registry, context);

    // 2. ACT: Translate
    Decl* result = orchestrator.translateDecl(cppClass);

    // 3. ASSERT: Verify C AST
    RecordDecl* cStruct = dyn_cast<RecordDecl>(result);
    ASSERT_NE(cStruct, nullptr);
    EXPECT_EQ(cStruct->getNameAsString(), "Counter");

    // Verify field exists
    auto fields = cStruct->fields();
    ASSERT_EQ(std::distance(fields.begin(), fields.end()), 1);
    EXPECT_EQ((*fields.begin())->getNameAsString(), "count");

    // Verify method was translated to separate function
    FunctionDecl* cMethod = context.lookupMethod(method);
    ASSERT_NE(cMethod, nullptr);
    EXPECT_EQ(cMethod->getNameAsString(), "Counter_increment");

    // Verify 'this' parameter added
    ASSERT_EQ(cMethod->getNumParams(), 1);
    ParmVarDecl* thisParam = cMethod->getParamDecl(0);
    EXPECT_EQ(thisParam->getNameAsString(), "this");
    EXPECT_TRUE(thisParam->getType()->isPointerType());
}
```

---

## End-to-End Integration Testing

### Objective
Test **complete transpilation** from C++ source to working C code.

### Test Structure

```cpp
class TranspilerIntegrationTest : public ::testing::Test {
protected:
    void testTranspilation(
        const std::string& cppCode,
        const std::string& expectedCCode,
        const std::string& inputData = "",
        const std::string& expectedOutput = ""
    ) {
        // 1. Write C++ code to temp file
        std::string cppFile = writeTempFile("test.cpp", cppCode);

        // 2. Run transpiler (all 3 stages)
        TranspilerOptions opts;
        Transpiler transpiler(opts);
        TranspilationResult result = transpiler.transpile(cppFile);

        ASSERT_TRUE(result.success) << result.errorMessage;

        // 3. Verify generated C code
        std::string actualCCode = readFile(result.outputFile);
        EXPECT_EQ(normalizeWhitespace(actualCCode),
                  normalizeWhitespace(expectedCCode));

        // 4. Compile generated C code
        bool compileSuccess = compileC(result.outputFile, result.executableFile);
        ASSERT_TRUE(compileSuccess) << "Generated C code does not compile";

        // 5. Run and verify output (if expected output provided)
        if (!expectedOutput.empty()) {
            std::string actualOutput = runExecutable(result.executableFile, inputData);
            EXPECT_EQ(actualOutput, expectedOutput);
        }
    }
};

TEST_F(TranspilerIntegrationTest, SimpleFunction) {
    testTranspilation(
        // C++ input
        R"(
            int add(int a, int b) {
                return a + b;
            }

            int main() {
                return add(3, 4);
            }
        )",

        // Expected C output
        R"(
            int add(int a, int b) {
                return a + b;
            }

            int main(void) {
                return add(3, 4);
            }
        )",

        // Input data
        "",

        // Expected output (return code)
        "7"  // Verified via exit code: echo $?
    );
}
```

### Verification Layers

1. **AST Verification**: C AST structure is correct
2. **Code Verification**: Generated C code matches expected
3. **Compilation Verification**: C code compiles without errors
4. **Runtime Verification**: Executable produces correct output

---

## Test Organization

### Directory Structure

```
tests/
├── unit/
│   └── handlers/
│       ├── FunctionHandlerTest.cpp
│       ├── VariableHandlerTest.cpp
│       ├── ExpressionHandlerTest.cpp
│       ├── StatementHandlerTest.cpp
│       ├── RecordHandlerTest.cpp
│       ├── MethodHandlerTest.cpp
│       ├── ConstructorHandlerTest.cpp
│       ├── EnumHandlerTest.cpp
│       └── TemplateHandlerTest.cpp
├── integration/
│   └── handlers/
│       ├── ClassTranslationTest.cpp
│       ├── MethodCallTranslationTest.cpp
│       ├── EnumSwitchTest.cpp
│       └── TemplateInstantiationTest.cpp
└── e2e/
    ├── phase1_basic_functions/
    │   ├── simple_function_test.cpp
    │   ├── arithmetic_test.cpp
    │   └── function_calls_test.cpp
    ├── phase2_control_flow/
    │   ├── if_else_test.cpp
    │   ├── loops_test.cpp
    │   └── switch_test.cpp
    ├── phase6_classes/
    │   ├── simple_class_test.cpp
    │   ├── constructor_test.cpp
    │   └── method_calls_test.cpp
    └── ...
```

---

## Test-Driven Development (TDD) Workflow

### Red-Green-Refactor Cycle

```
┌──────────────────────────────────────────┐
│ 1. RED: Write failing unit test         │
│    - Test what handler SHOULD do         │
│    - Test fails (handler not implemented)│
└────────────┬─────────────────────────────┘
             │
             ▼
┌──────────────────────────────────────────┐
│ 2. GREEN: Implement minimal handler      │
│    - Make test pass                      │
│    - Don't worry about elegance yet      │
└────────────┬─────────────────────────────┘
             │
             ▼
┌──────────────────────────────────────────┐
│ 3. REFACTOR: Clean up implementation     │
│    - Keep tests passing                  │
│    - Improve design                      │
└────────────┬─────────────────────────────┘
             │
             ▼
┌──────────────────────────────────────────┐
│ 4. REPEAT: Add next test case            │
│    - Edge case, different scenario       │
│    - Cycle continues                     │
└──────────────────────────────────────────┘
```

### Example TDD Progression for FunctionHandler

**Iteration 1**: Simple function
```cpp
TEST(FunctionHandlerTest, EmptyFunction) {
    // void foo() {}
}
```

**Iteration 2**: With return type
```cpp
TEST(FunctionHandlerTest, IntReturnType) {
    // int bar() { return 0; }
}
```

**Iteration 3**: With parameters
```cpp
TEST(FunctionHandlerTest, WithParameters) {
    // int add(int a, int b) { return a + b; }
}
```

**Iteration 4**: Multiple parameters
```cpp
TEST(FunctionHandlerTest, MultipleParameters) {
    // int sum(int a, int b, int c) { return a + b + c; }
}
```

**Iteration 5**: Pointer parameters
```cpp
TEST(FunctionHandlerTest, PointerParameters) {
    // void modify(int* ptr) { *ptr = 10; }
}
```

Each iteration adds ONE new requirement, ONE new test.

---

## Mock and Fixture Utilities

### MockASTContext

```cpp
class MockASTContext {
    std::unique_ptr<ASTContext> ctx;
    std::vector<std::unique_ptr<Decl>> ownedDecls;

public:
    MockASTContext();

    ASTContext& getContext() { return *ctx; }

    FunctionDecl* createFunction(...);
    VarDecl* createVariable(...);
    BinaryOperator* createBinaryOp(...);
    // ... builder methods

    ~MockASTContext(); // Cleans up owned AST nodes
};
```

### HandlerTestFixture

```cpp
class HandlerTestFixture : public ::testing::Test {
protected:
    MockASTContext cppCtx;
    MockASTContext cCtx;
    CNodeBuilder builder;
    HandlerContext context;

    HandlerTestFixture()
        : builder(cCtx.getContext()),
          context(cppCtx.getContext(), cCtx.getContext(), builder) {}

    // Helper methods available to all tests
    template<typename Handler>
    Decl* translate(Decl* cppDecl) {
        Handler handler;
        return handler.handleDecl(cppDecl, context);
    }
};

// Usage
class FunctionHandlerTest : public HandlerTestFixture {};

TEST_F(FunctionHandlerTest, SimpleFunction) {
    FunctionDecl* cppFunc = cppCtx.createFunction("int", "add", {"int a"});
    Decl* result = translate<FunctionHandler>(cppFunc);
    // ... assertions
}
```

---

## Coverage Requirements

### Unit Test Coverage
- **Target**: 100% line coverage for each handler
- **Metric**: Every code path in handler exercised
- **Tools**: `gcov`, `lcov`, `llvm-cov`

### Handler Integration Coverage
- **Target**: 90% coverage of handler interactions
- **Metric**: All handler dependencies tested
- **Focus**: Complex scenarios (class with methods, templates, inheritance)

### E2E Coverage
- **Target**: 100% of supported C++ features
- **Metric**: At least one E2E test per feature in roadmap
- **Progression**: Phase 1 → Phase 12

---

## Continuous Integration

### CI Pipeline

```yaml
# .github/workflows/tests.yml
name: Tests

on: [push, pull_request]

jobs:
  unit-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Build
        run: cmake -B build && cmake --build build
      - name: Run unit tests
        run: cd build && ctest --output-on-failure -R "Unit.*"

  integration-tests:
    runs-on: ubuntu-latest
    needs: unit-tests
    steps:
      - uses: actions/checkout@v2
      - name: Build
        run: cmake -B build && cmake --build build
      - name: Run integration tests
        run: cd build && ctest --output-on-failure -R "Integration.*"

  e2e-tests:
    runs-on: ubuntu-latest
    needs: integration-tests
    steps:
      - uses: actions/checkout@v2
      - name: Build
        run: cmake -B build && cmake --build build
      - name: Run E2E tests
        run: cd build && ctest --output-on-failure -R "E2E.*"

  coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Build with coverage
        run: cmake -B build -DCMAKE_BUILD_TYPE=Coverage
      - name: Run all tests
        run: cd build && ctest
      - name: Generate coverage report
        run: |
          cd build
          lcov --capture --directory . --output-file coverage.info
          lcov --remove coverage.info '/usr/*' --output-file coverage.info
          lcov --list coverage.info
      - name: Upload to Codecov
        uses: codecov/codecov-action@v2
```

---

## Summary

### Testing Strategy at a Glance

| Test Level | Count | What | How | When |
|------------|-------|------|-----|------|
| **Unit** | 50+ per handler | AST → AST | Mocks, matchers | Every commit |
| **Integration** | 20-30 per phase | Multi-handler | Real handlers | Per feature |
| **E2E** | 5-10 per phase | C++ → C | Full pipeline | Per phase |

### Key Principles

1. **Test BEFORE implementing** (TDD)
2. **Unit tests verify AST structure**, not code text
3. **Integration tests verify handler cooperation**
4. **E2E tests verify compiled C code works**
5. **100% coverage for handlers** (they're the core logic)
6. **Automated CI** runs all tests on every commit

### Benefits

✅ **Catch bugs early** - Unit tests fail immediately
✅ **Surgical debugging** - Know exactly which handler broke
✅ **Refactor safely** - Tests ensure no regression
✅ **Document behavior** - Tests show how handlers work
✅ **Enable TDD** - Write test, implement, refactor
