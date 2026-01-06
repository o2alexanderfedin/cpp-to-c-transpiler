# Group 5 Task 9: E2E Tests

**Task**: Create end-to-end executable tests for virtual methods
**Status**: PENDING
**Tests Required**: 15 tests (1-3 active, rest disabled)
**Estimated Time**: 2-3 hours

## Task Description

Create `tests/e2e/phase45/VirtualMethodsE2ETest.cpp` that compiles generated C code and executes it to verify runtime behavior.

## Requirements

1. **Compile generated C**: Use system C compiler
2. **Execute and verify**: Run compiled binary, check output/behavior
3. **Runtime polymorphism**: Verify virtual dispatch works at runtime
4. **Keep most disabled**: Only 1-3 active tests, rest DISABLED_ prefix

## Implementation Strategy (TDD)

### Test File
`tests/e2e/phase45/VirtualMethodsE2ETest.cpp`

### Tests to Create (15 tests)

#### Active Tests (1-3)
1. **SimpleVirtualCall**: Single class, single virtual method, call it
2. **PolymorphicDispatch**: Base pointer → derived method execution
3. **VirtualCallWithReturnValue**: Virtual method returns value, verify it

#### Disabled Algorithm Tests (12)
4. **DISABLED_ShapeHierarchy**: Circle and Rectangle from Shape
5. **DISABLED_AnimalHierarchy**: Dog and Cat from Animal
6. **DISABLED_StackInterface**: Stack interface with array/list implementations
7. **DISABLED_ListInterface**: List interface with variations
8. **DISABLED_IteratorPattern**: Iterator over polymorphic collection
9. **DISABLED_StrategyPattern**: Strategy pattern implementation
10. **DISABLED_ObserverPattern**: Observer/observable pattern
11. **DISABLED_FactoryPattern**: Factory creating polymorphic objects
12. **DISABLED_PluginSystem**: Plugin architecture with interface
13. **DISABLED_EventHandlerSystem**: Event handlers with virtual dispatch
14. **DISABLED_StatePattern**: State machine with virtual states
15. **DISABLED_VisitorPattern**: Visitor pattern with double dispatch

## Example Active Test

```cpp
TEST_F(VirtualMethodsE2ETest, SimpleVirtualCall) {
    const char* cppCode = R"(
        #include <stdio.h>

        class Animal {
        public:
            virtual void speak() {
                printf("Animal sound\n");
            }
        };

        int main() {
            Animal a;
            a.speak();
            return 0;
        }
    )";

    // Transpile to C
    std::string cCode = transpile(cppCode);

    // Compile C code
    std::string executable = compileC(cCode);

    // Execute and capture output
    std::string output = execute(executable);

    // Verify output
    EXPECT_EQ(output, "Animal sound\n");
}
```

## Example Disabled Test

```cpp
TEST_F(VirtualMethodsE2ETest, DISABLED_PolymorphicAlgorithm) {
    const char* cppCode = R"(
        #include <stdio.h>

        class Shape {
        public:
            virtual ~Shape() {}
            virtual double area() = 0;
        };

        class Circle : public Shape {
            double radius;
        public:
            Circle(double r) : radius(r) {}
            virtual double area() { return 3.14159 * radius * radius; }
        };

        class Rectangle : public Shape {
            double width, height;
        public:
            Rectangle(double w, double h) : width(w), height(h) {}
            virtual double area() { return width * height; }
        };

        void printArea(Shape* shape) {
            printf("Area: %.2f\n", shape->area());
        }

        int main() {
            Circle c(5.0);
            Rectangle r(4.0, 6.0);

            printArea(&c);
            printArea(&r);

            return 0;
        }
    )";

    std::string cCode = transpile(cppCode);
    std::string executable = compileC(cCode);
    std::string output = execute(executable);

    EXPECT_THAT(output, HasSubstr("Area: 78.54"));  // Circle
    EXPECT_THAT(output, HasSubstr("Area: 24.00"));  // Rectangle
}
```

## Compilation Helper

```cpp
class VirtualMethodsE2ETest : public ::testing::Test {
protected:
    std::string transpile(const std::string& cppCode) {
        // Use transpiler API
        // Return generated C code
    }

    std::string compileC(const std::string& cCode) {
        // Write to temp file
        // Invoke: gcc -o output temp.c
        // Return path to executable
    }

    std::string execute(const std::string& executable) {
        // Run executable
        // Capture stdout
        // Return output
    }
};
```

## Test Categories

### Sanity (1 active)
- Basic virtual call works

### Polymorphic Dispatch (2 active)
- Base pointer calls derived method
- Virtual call returns correct value

### Disabled Algorithms (12)
- Design patterns
- Data structures
- Complex hierarchies
- Real-world scenarios

## Files to Create

- `tests/e2e/phase45/VirtualMethodsE2ETest.cpp`

## Success Criteria

- All 1-3 active tests pass and execute correctly
- Generated C code compiles without errors
- Runtime polymorphic dispatch works
- Disabled tests are properly structured (ready to enable later)
- Tests demonstrate practical use cases
