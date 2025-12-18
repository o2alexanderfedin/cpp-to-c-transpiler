# Contributing Guide

**How to Contribute to the C++ to C Transpiler**

Thank you for your interest in contributing! This guide will help you get started.

## Table of Contents

1. [Getting Started](#getting-started)
2. [Development Process](#development-process)
3. [Code Standards](#code-standards)
4. [Testing Requirements](#testing-requirements)
5. [Submitting Changes](#submitting-changes)
6. [Areas for Contribution](#areas-for-contribution)

## Getting Started

### Prerequisites

- C++17 compiler (GCC 8+, Clang 10+)
- CMake 3.20+
- Clang/LLVM 15+ (LibTooling)
- Git
- (Optional) Frama-C for verification testing

### Building from Source

```bash
# Clone repository
git clone https://github.com/o2alexanderfedin/cpp-to-c-transpiler.git
cd cpp-to-c-transpiler

# Install dependencies (macOS)
brew install llvm cmake

# Configure build
export CMAKE_PREFIX_PATH="/opt/homebrew/opt/llvm"
cmake -B build -DCMAKE_BUILD_TYPE=Debug

# Build
cmake --build build

# Run tests
./tests/build_test.sh
./tests/libtooling_test.sh
./tests/visitor_test.sh
```

### Project Structure

```
cpp-to-c-transpiler/
├── include/          # Header files
├── src/              # Source files
├── runtime/          # Runtime library
├── tests/            # Test suite
├── examples/         # Example projects
├── docs/             # Documentation
└── CMakeLists.txt    # Build configuration
```

## Development Process

We follow **Test-Driven Development (TDD)** and **SOLID principles**.

### TDD Workflow

1. **RED**: Write a failing test first
2. **GREEN**: Write minimal code to pass
3. **REFACTOR**: Improve code while keeping tests green

### Example TDD Session

```cpp
// 1. RED: Write failing test
TEST(CNodeBuilder, CreateIntVariable) {
    ASTContext &Ctx = getTestContext();
    CNodeBuilder builder(Ctx);

    VarDecl *var = builder.intVar("x", 42);

    ASSERT_NE(var, nullptr);
    ASSERT_EQ(var->getName(), "x");
    ASSERT_EQ(getInitValue(var), 42);
}
// Build: FAIL (intVar not implemented)

// 2. GREEN: Minimal implementation
VarDecl* CNodeBuilder::intVar(StringRef name, int initVal) {
    QualType intType = Ctx.IntTy;
    VarDecl *var = VarDecl::Create(
        Ctx, /*DC=*/Ctx.getTranslationUnitDecl(),
        SourceLocation(), SourceLocation(),
        &Ctx.Idents.get(name), intType,
        Ctx.getTrivialTypeSourceInfo(intType),
        SC_None);

    IntegerLiteral *init = IntegerLiteral::Create(
        Ctx, APInt(32, initVal), intType, SourceLocation());
    var->setInit(init);

    return var;
}
// Build: PASS

// 3. REFACTOR: Extract helper
VarDecl* CNodeBuilder::createVarDecl(QualType type, StringRef name) {
    return VarDecl::Create(
        Ctx, Ctx.getTranslationUnitDecl(),
        SourceLocation(), SourceLocation(),
        &Ctx.Idents.get(name), type,
        Ctx.getTrivialTypeSourceInfo(type),
        SC_None);
}

VarDecl* CNodeBuilder::intVar(StringRef name, int initVal) {
    VarDecl *var = createVarDecl(Ctx.IntTy, name);
    IntegerLiteral *init = IntegerLiteral::Create(
        Ctx, APInt(32, initVal), Ctx.IntTy, SourceLocation());
    var->setInit(init);
    return var;
}
// Build: PASS (cleaner code)
```

### Git Workflow

We use Git Flow (or simplified version for solo developers):

```bash
# Create feature branch
git checkout -b feature/add-coroutine-support

# Make changes (commit frequently)
git add src/CoroutineDetector.cpp tests/coroutine_test.cpp
git commit -m "feat: implement coroutine detection

- Add CoroutineDetector class
- Detect co_await, co_yield, co_return
- Add unit tests for detection

Refs: #42"

# Push to remote
git push origin feature/add-coroutine-support

# Create pull request (if collaborative)
# OR merge directly (if solo)
git checkout main
git merge feature/add-coroutine-support
git push origin main

# Tag release (for significant features)
git tag -a v1.2.0 -m "Add coroutine support"
git push origin v1.2.0
```

## Code Standards

### SOLID Principles

We religiously follow SOLID:

1. **Single Responsibility**: Each class has one reason to change
2. **Open/Closed**: Open for extension, closed for modification
3. **Liskov Substitution**: Subtypes must be substitutable
4. **Interface Segregation**: Many specific interfaces > one general
5. **Dependency Inversion**: Depend on abstractions, not concretions

### Code Style

#### Naming Conventions

```cpp
// Classes: PascalCase
class VtableGenerator { };

// Functions: camelCase
void generateVtable() { }

// Variables: camelCase
int nodeCount = 0;

// Constants: UPPER_SNAKE_CASE
constexpr int MAX_BUFFER_SIZE = 1024;

// Private members: camelCase with trailing underscore (optional)
class MyClass {
    int value_;
};
```

#### File Organization

```cpp
// Header file: FeatureName.h
#pragma once  // Or include guards

#include <clang/AST/Decl.h>
#include "CNodeBuilder.h"

namespace cpptoc {

class FeatureTranslator {
public:
    explicit FeatureTranslator(ASTContext &Ctx);

    // Public API
    Decl* translate(CXXRecordDecl *Class);

private:
    // Private helpers
    void analyzeFeature();

    // Data members
    ASTContext &Ctx;
    CNodeBuilder Builder;
};

} // namespace cpptoc
```

#### Comments

```cpp
// Good: Why, not what
// Use RAII to ensure cleanup even on exception
class Resource {
    ~Resource() { cleanup(); }
};

// Bad: Obvious what
// Increment counter by one
counter++;

// Function documentation
/**
 * Generate vtable structure for polymorphic class.
 *
 * Creates a struct containing function pointers for all virtual methods.
 * Handles single and multiple inheritance, but not virtual inheritance.
 *
 * @param Class The C++ class declaration
 * @return Generated vtable struct declaration
 * @pre Class must have at least one virtual function
 */
RecordDecl* generateVtableStruct(CXXRecordDecl *Class);
```

### Clang Coding Conventions

Follow Clang's conventions when working with Clang APIs:

```cpp
// Use Clang's naming for AST nodes
CXXRecordDecl *Class = ...;  // Not: class_decl
FunctionDecl *Func = ...;    // Not: function

// Use dyn_cast for safe casting
if (CXXMethodDecl *Method = dyn_cast<CXXMethodDecl>(D)) {
    // Use Method
}

// Use llvm::StringRef for string parameters
void processName(StringRef name) { }  // Not: const std::string&
```

## Testing Requirements

### Unit Tests

Every new feature must have unit tests:

```cpp
// tests/cnode_builder_test.cpp
#include "CNodeBuilder.h"
#include <gtest/gtest.h>

class CNodeBuilderTest : public ::testing::Test {
protected:
    ASTContext* Ctx;

    void SetUp() override {
        Ctx = createTestContext();
    }
};

TEST_F(CNodeBuilderTest, CreateIntVariable) {
    CNodeBuilder builder(*Ctx);
    VarDecl *var = builder.intVar("x", 42);

    ASSERT_NE(var, nullptr);
    EXPECT_EQ(var->getName(), "x");
}

TEST_F(CNodeBuilderTest, CreateFunctionCall) {
    CNodeBuilder builder(*Ctx);

    CallExpr *call = builder.call("printf", {
        builder.stringLiteral("Hello, World!")
    });

    ASSERT_NE(call, nullptr);
    EXPECT_EQ(call->getNumArgs(), 1);
}
```

### Integration Tests

Test complete translations:

```cpp
// tests/integration/simple_class_test.cpp
TEST(IntegrationTest, TranslateSimpleClass) {
    std::string input = R"(
        class Point {
            int x, y;
        public:
            Point(int x, int y) : x(x), y(y) {}
            int getX() { return x; }
        };
    )";

    std::string output = transpile(input);

    // Verify struct generated
    EXPECT_THAT(output, HasSubstr("struct Point {"));
    EXPECT_THAT(output, HasSubstr("int x;"));
    EXPECT_THAT(output, HasSubstr("int y;"));

    // Verify functions generated
    EXPECT_THAT(output, HasSubstr("void Point_ctor("));
    EXPECT_THAT(output, HasSubstr("int Point_getX("));

    // Verify it compiles
    EXPECT_TRUE(compileC(output));
}
```

### Regression Tests

Keep tests for fixed bugs:

```cpp
// tests/regression/issue_42_test.cpp
// Regression test for Issue #42: Virtual inheritance crash
TEST(RegressionTest, Issue42_VirtualInheritanceCrash) {
    std::string input = R"(
        class Base { virtual ~Base() {} };
        class Left : public virtual Base {};
        class Right : public virtual Base {};
        class Diamond : public Left, public Right {};
    )";

    // Should not crash
    ASSERT_NO_THROW({
        std::string output = transpile(input);
    });
}
```

### Test Coverage

Aim for high coverage:

```bash
# Generate coverage report
cmake -B build -DCMAKE_BUILD_TYPE=Debug -DENABLE_COVERAGE=ON
cmake --build build
ctest --test-dir build
gcovr -r . --html --html-details -o coverage.html

# Target: > 80% line coverage
```

## Submitting Changes

### Commit Messages

Follow [Conventional Commits](https://www.conventionalcommits.org/):

```
type(scope): subject

[optional body]

[optional footer]
```

**Types**:
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation
- `refactor`: Code refactoring
- `test`: Add/update tests
- `chore`: Maintenance

**Examples**:

```
feat(vtable): add support for multiple inheritance

Implement pointer adjustment thunks for multiple inheritance.
Generates offset calculations for each base class.

Closes #123

---

fix(exception): correct action table ordering

Action tables were in wrong order causing destructors to be
called in incorrect sequence. Now reversed to match C++ semantics.

Fixes #456

---

docs(architecture): add coroutine implementation guide

Add detailed documentation for coroutine state machine
transformation with examples and diagrams.
```

### Pull Request Process

1. **Create feature branch**: `git checkout -b feature/my-feature`
2. **Write tests first** (TDD RED phase)
3. **Implement feature** (TDD GREEN phase)
4. **Refactor** (TDD REFACTOR phase)
5. **Run all tests**: `./tests/run_all.sh`
6. **Run linters**: `./tools/lint.sh`
7. **Update documentation**
8. **Commit with conventional message**
9. **Push to remote**
10. **Create pull request**
11. **Address review feedback**
12. **Merge when approved**

### Code Review Checklist

Reviewers check:

- [ ] Tests pass (all green)
- [ ] Code follows SOLID principles
- [ ] No duplicate code (DRY)
- [ ] Clear names and comments
- [ ] Documentation updated
- [ ] No performance regressions
- [ ] Memory safety (no leaks)
- [ ] Error handling present
- [ ] Edge cases covered

## Areas for Contribution

### High Priority

1. **Exception Handling**: Complete PNaCl SJLJ implementation
2. **RTTI Support**: Implement dynamic_cast and typeid
3. **Virtual Inheritance**: VTT generation
4. **Coroutines**: State machine transformation
5. **Template Monomorphization**: STL support

### Medium Priority

1. **Lambda Expressions**: Closure generation
2. **Move Semantics**: Rvalue references
3. **Smart Pointers**: shared_ptr, unique_ptr
4. **Frama-C Integration**: ACSL annotation generation
5. **Size Optimization**: Reduce generated code size

### Low Priority (Nice to Have)

1. **Debug Info**: Preserve source locations
2. **Pretty Printing**: Format generated code
3. **Error Messages**: Improve diagnostic output
4. **Performance**: Optimize translation speed
5. **Documentation**: More examples and guides

### Good First Issues

Start with these beginner-friendly tasks:

- Add more CNodeBuilder helper functions
- Write additional test cases
- Improve documentation and examples
- Fix compiler warnings
- Add error messages

## Communication

- **Issues**: Use GitHub Issues for bugs and features
- **Discussions**: Use GitHub Discussions for questions
- **Email**: Contact maintainers for sensitive issues

## License

By contributing, you agree that your contributions will be licensed under the project's license (CC BY-NC-ND 4.0 for non-commercial, commercial license available).

## Recognition

Contributors will be recognized in:
- CONTRIBUTORS.md
- Release notes
- Documentation credits

Thank you for contributing to the C++ to C Transpiler!

---

**Document Version**: 1.0
**Last Updated**: 2025-12-18
**See Also**: [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md), [ARCHITECTURE.md](../ARCHITECTURE.md)
