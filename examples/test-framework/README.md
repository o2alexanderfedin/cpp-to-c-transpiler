# Unit Test Framework Example

This example demonstrates a minimal C++ unit test framework transpiled to C, showcasing complex features.

## Overview

A lightweight testing framework demonstrating:

1. **Template Meta-Programming**: Type-safe assertions
2. **Multiple Inheritance**: Test fixtures with mixins
3. **RAII for Setup/Teardown**: Automatic resource management
4. **Exception-Based Assertions**: Test failure handling
5. **Macro-Based Test Registration**: Compile-time test discovery

## Features

### 1. Test Case Definition

```cpp
TEST(MathTests, Addition) {
    ASSERT_EQ(2 + 2, 4);
    ASSERT_EQ(10 + 5, 15);
}

TEST(MathTests, Division) {
    ASSERT_EQ(10 / 2, 5);
    ASSERT_THROWS(divide(10, 0), DivideByZeroError);
}
```

### 2. Test Fixtures (RAII)

```cpp
class DatabaseTest : public TestFixture {
protected:
    Database* db;

    void SetUp() override {
        db = new Database(":memory:");
        db->connect();
    }

    void TearDown() override {
        db->disconnect();
        delete db;
    }
};

TEST_F(DatabaseTest, InsertRecord) {
    db->insert("test_table", data);
    ASSERT_EQ(db->count("test_table"), 1);
}
```

### 3. Assertions

```cpp
// Equality
ASSERT_EQ(actual, expected);
ASSERT_NE(actual, unexpected);

// Comparisons
ASSERT_LT(a, b);   // Less than
ASSERT_LE(a, b);   // Less or equal
ASSERT_GT(a, b);   // Greater than
ASSERT_GE(a, b);   // Greater or equal

// Boolean
ASSERT_TRUE(condition);
ASSERT_FALSE(condition);

// Exceptions
ASSERT_THROWS(expression, ExceptionType);
ASSERT_NO_THROW(expression);
```

### 4. Test Suites

```cpp
class MathTests : public TestSuite {
public:
    void addTests() override {
        ADD_TEST(testAddition);
        ADD_TEST(testSubtraction);
        ADD_TEST(testMultiplication);
    }
};
```

## Building

```bash
mkdir build
cd build
cmake ..
make
./test-framework-example
```

## Expected Output

```
Test Framework Example
======================

Running tests...

[==========] Running 12 tests from 3 test suites
[----------] 4 tests from MathTests
[ RUN      ] MathTests.Addition
[       OK ] MathTests.Addition (0 ms)
[ RUN      ] MathTests.Subtraction
[       OK ] MathTests.Subtraction (0 ms)
[ RUN      ] MathTests.Multiplication
[       OK ] MathTests.Multiplication (0 ms)
[ RUN      ] MathTests.DivisionByZero
[       OK ] MathTests.DivisionByZero (0 ms)
[----------] 4 tests from MathTests (0 ms total)

[----------] 5 tests from StringTests
[ RUN      ] StringTests.Concatenation
[       OK ] StringTests.Concatenation (0 ms)
[ RUN      ] StringTests.Length
[       OK ] StringTests.Length (0 ms)
[ RUN      ] StringTests.Substring
[       OK ] StringTests.Substring (0 ms)
[ RUN      ] StringTests.Find
[       OK ] StringTests.Find (0 ms)
[ RUN      ] StringTests.Replace
[       OK ] StringTests.Replace (0 ms)
[----------] 5 tests from StringTests (1 ms total)

[----------] 3 tests from FixtureTests
[ RUN      ] FixtureTests.Setup
[       OK ] FixtureTests.Setup (0 ms)
[ RUN      ] FixtureTests.TearDown
[       OK ] FixtureTests.TearDown (0 ms)
[ RUN      ] FixtureTests.Resource
[       OK ] FixtureTests.Resource (0 ms)
[----------] 3 tests from FixtureTests (0 ms total)

[==========] 12 tests from 3 test suites ran. (1 ms total)
[  PASSED  ] 12 tests
```

## Architecture

### Class Hierarchy

```
TestCase (base)
├── Test (simple test)
└── TestFixture (with setup/teardown)
    ├── DatabaseTest
    ├── FileSystemTest
    └── NetworkTest

TestSuite
├── contains: vector<TestCase*>
└── manages: test execution
```

### Generated C Structures

```c
// TestCase vtable
struct TestCase_vtable {
    void (*run)(void* this);
    void (*setUp)(void* this);
    void (*tearDown)(void* this);
};

struct TestCase {
    const struct TestCase_vtable* vptr;
    const char* name;
    bool passed;
};

// Test results
struct TestResult {
    int total_tests;
    int passed_tests;
    int failed_tests;
    double elapsed_time_ms;
};
```

## Complex Features Demonstrated

### 1. Template-Based Assertions

```cpp
template<typename T>
void assertEqual(const T& expected, const T& actual,
                const char* file, int line) {
    if (!(expected == actual)) {
        throw AssertionError(file, line, "Values not equal");
    }
}

// Generated C (monomorphized)
void assertEqual_int(int expected, int actual,
                     const char* file, int line);
void assertEqual_double(double expected, double actual,
                        const char* file, int line);
void assertEqual_cstr(const char* expected, const char* actual,
                      const char* file, int line);
```

### 2. Multiple Inheritance (Mixins)

```cpp
class Printable {
public:
    virtual void print() = 0;
};

class Comparable {
public:
    virtual bool equals(const Comparable* other) = 0;
};

class TestResult : public Printable, public Comparable {
    void print() override;
    bool equals(const Comparable* other) override;
};
```

### 3. Exception-Based Control Flow

```cpp
void runTest(TestCase* test) {
    try {
        test->setUp();
        test->run();
        test->tearDown();
        test->markPassed();
    } catch (const AssertionError& e) {
        test->markFailed(e.getMessage());
    } catch (const std::exception& e) {
        test->markFailed("Unexpected exception");
    }
}
```

### 4. RAII for Test Fixtures

```cpp
class FileSystemTest : public TestFixture {
    char temp_dir[256];

    void SetUp() override {
        snprintf(temp_dir, sizeof(temp_dir), "/tmp/test_%d", getpid());
        mkdir(temp_dir, 0755);
    }

    void TearDown() override {
        removeDirectory(temp_dir);  // Automatic cleanup
    }
};
```

## Use Cases

### 1. Unit Testing

```cpp
TEST(Calculator, BasicOperations) {
    Calculator calc;
    ASSERT_EQ(calc.add(2, 3), 5);
    ASSERT_EQ(calc.subtract(10, 4), 6);
    ASSERT_EQ(calc.multiply(3, 7), 21);
}
```

### 2. Integration Testing

```cpp
TEST_F(DatabaseTest, TransactionRollback) {
    db->beginTransaction();
    db->insert("users", user1);
    db->insert("users", user2);
    db->rollback();

    ASSERT_EQ(db->count("users"), 0);
}
```

### 3. Property-Based Testing

```cpp
TEST(SortTests, SortedArraysAreOrdered) {
    for (int i = 0; i < 100; i++) {
        int arr[10];
        generateRandomArray(arr, 10);
        sort(arr, 10);

        // Verify sorted
        for (int j = 0; j < 9; j++) {
            ASSERT_LE(arr[j], arr[j+1]);
        }
    }
}
```

## File Structure

```
test-framework/
├── README.md
├── CMakeLists.txt
├── src/
│   ├── main.cpp              # Test runner
│   ├── test_framework.h      # Framework core
│   ├── assertions.h          # Assertion macros
│   ├── test_case.h           # TestCase base
│   ├── test_fixture.h        # Fixture support
│   └── test_suite.h          # Suite management
└── generated/                # Generated C
    ├── test_framework.c
    └── test_framework.h
```

## Performance

| Operation | Time |
|-----------|------|
| Test registration | Compile-time |
| Setup/teardown | 0.05 ms |
| Assertion | 0.02 ms |
| Exception throw/catch | 2.0 ms |

## Best Practices

### 1. One Assertion Per Test

```cpp
// Good
TEST(Math, Addition) {
    ASSERT_EQ(add(2, 3), 5);
}

TEST(Math, Subtraction) {
    ASSERT_EQ(subtract(5, 3), 2);
}

// Bad: Multiple unrelated assertions
TEST(Math, Everything) {
    ASSERT_EQ(add(2, 3), 5);
    ASSERT_EQ(subtract(5, 3), 2);  // If this fails, add() not tested
}
```

### 2. Use Fixtures for Setup

```cpp
// Good: Reusable setup
class DatabaseTest : public TestFixture {
    void SetUp() override { /* setup */ }
};

// Bad: Duplicate setup
TEST(Database, Test1) {
    Database db;  // Duplicate
    db.connect();
    // ...
}
```

## Further Reading

- `../../docs/TESTING.md` - Testing best practices
- `../../docs/EXCEPTIONS.md` - Exception handling
- Google Test documentation
- xUnit patterns
