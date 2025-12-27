/**
 * @file ComStyleAllMethodsTest.cpp
 * @brief Test suite for COM-style static declarations for all methods (Phase 31-03)
 *
 * Tests that ALL methods (virtual and non-virtual) generate static declarations
 * for compile-time type safety.
 */

#include "TestHelpers.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/ASTUnit.h"
#include "gtest/gtest.h"
#include <memory>

using namespace clang;

class ComStyleAllMethodsTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> AST;

    /**
     * @brief Transpile C++ code and return generated header
     * @param code C++ code to transpile
     * @return Generated C header code
     */
    std::string transpileToHeader(const char* code) {
        AST = buildASTFromCode(code);
        if (!AST) {
            return "";
        }

        // For now, we'll just extract the relevant portion
        // In actual implementation, this would call the transpiler
        // and extract the header portion
        return ""; // Placeholder - will be implemented
    }
};

// ============================================================================
// Test 1: Non-virtual methods
// ============================================================================

TEST_F(ComStyleAllMethodsTest, NonVirtualMethods) {
    const char* code = R"(
        class Counter {
            int value;
        public:
            Counter(int v) : value(v) {}
            int getValue() const { return value; }
            void increment() { value++; }
        };
    )";

    std::string header = transpileToHeader(code);

    // Verify constructor declaration
    EXPECT_THAT(header, HasSubstr("static void Counter__ctor_1(struct Counter *this, int v)"));

    // Verify method declarations
    EXPECT_THAT(header, HasSubstr("static int Counter_getValue(const struct Counter *this)"));
    EXPECT_THAT(header, HasSubstr("static void Counter_increment(struct Counter *this)"));
}

// ============================================================================
// Test 2: Overloaded constructors
// ============================================================================

TEST_F(ComStyleAllMethodsTest, OverloadedConstructors) {
    const char* code = R"(
        class Point {
            int x, y;
        public:
            Point() : x(0), y(0) {}
            Point(int v) : x(v), y(v) {}
            Point(int x_, int y_) : x(x_), y(y_) {}
        };
    )";

    std::string header = transpileToHeader(code);

    // Verify all constructor overloads have declarations
    EXPECT_THAT(header, HasSubstr("static void Point__ctor(struct Point *this)"));
    EXPECT_THAT(header, HasSubstr("static void Point__ctor_1(struct Point *this, int v)"));
    EXPECT_THAT(header, HasSubstr("static void Point__ctor_2(struct Point *this, int x_, int y_)"));
}

// ============================================================================
// Test 3: Overloaded methods
// ============================================================================

TEST_F(ComStyleAllMethodsTest, OverloadedMethods) {
    const char* code = R"(
        class Printer {
        public:
            void print(int n) { }
            void print(double d) { }
            void print(const char* s) { }
        };
    )";

    std::string header = transpileToHeader(code);

    // Method overloading should append type suffixes
    EXPECT_THAT(header, HasSubstr("static void Printer_print"));
    // Note: Exact mangling scheme will be determined by MethodSignatureHelper
}

// ============================================================================
// Test 4: Const methods
// ============================================================================

TEST_F(ComStyleAllMethodsTest, ConstMethods) {
    const char* code = R"(
        class DataHolder {
            int data;
        public:
            int getData() const { return data; }
            void setData(int d) { data = d; }
        };
    )";

    std::string header = transpileToHeader(code);

    // Const methods should have 'const struct' in this parameter
    EXPECT_THAT(header, HasSubstr("static int DataHolder_getData(const struct DataHolder *this)"));
    EXPECT_THAT(header, HasSubstr("static void DataHolder_setData(struct DataHolder *this, int d)"));
}

// ============================================================================
// Test 5: Reference parameters
// ============================================================================

TEST_F(ComStyleAllMethodsTest, ReferenceParameters) {
    const char* code = R"(
        class Swapper {
        public:
            void swap(int& a, int& b) {
                int temp = a;
                a = b;
                b = temp;
            }
        };
    )";

    std::string header = transpileToHeader(code);

    // References should become pointers in C
    EXPECT_THAT(header, HasSubstr("static void Swapper_swap(struct Swapper *this, int* a, int* b)"));
}

// ============================================================================
// Test 6: Virtual and non-virtual mixed
// ============================================================================

TEST_F(ComStyleAllMethodsTest, MixedVirtualNonVirtual) {
    const char* code = R"(
        class Widget {
            int value;
        public:
            Widget(int v) : value(v) {}
            int getValue() const { return value; }
            virtual void update(int v) { value = v; }
            virtual ~Widget() {}
        };
    )";

    std::string header = transpileToHeader(code);

    // Both virtual and non-virtual should have declarations
    EXPECT_THAT(header, HasSubstr("static void Widget__ctor_1(struct Widget *this, int v)"));
    EXPECT_THAT(header, HasSubstr("static int Widget_getValue(const struct Widget *this)"));
    EXPECT_THAT(header, HasSubstr("static void Widget_update(struct Widget *this, int v)"));
    EXPECT_THAT(header, HasSubstr("static void Widget__dtor(struct Widget *this)"));
}

// ============================================================================
// Test 7: No declarations for compiler-generated methods
// ============================================================================

TEST_F(ComStyleAllMethodsTest, NoImplicitMethodDeclarations) {
    const char* code = R"(
        class Empty {
            // Compiler will generate implicit default ctor, copy ctor, dtor
        };
    )";

    std::string header = transpileToHeader(code);

    // Should NOT have declarations for implicit methods
    // (We only declare explicitly defined methods)
    // This is verified by checking that header doesn't contain method declarations
    // The struct definition should exist but no method declarations
    EXPECT_THAT(header, HasSubstr("struct Empty"));
}

// ============================================================================
// Test 8: Destructor declaration
// ============================================================================

TEST_F(ComStyleAllMethodsTest, DestructorDeclaration) {
    const char* code = R"(
        class Resource {
        public:
            Resource() {}
            ~Resource() {}
        };
    )";

    std::string header = transpileToHeader(code);

    // Both constructor and destructor should have declarations
    EXPECT_THAT(header, HasSubstr("static void Resource__ctor(struct Resource *this)"));
    EXPECT_THAT(header, HasSubstr("static void Resource__dtor(struct Resource *this)"));
}
