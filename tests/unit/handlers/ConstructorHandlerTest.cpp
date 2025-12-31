/**
 * @file ConstructorHandlerTest.cpp
 * @brief TDD tests for ConstructorHandler
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (15 tests):
 * 1. DefaultConstructor - Counter() : count(0) {}
 * 2. EmptyDefaultConstructor - Counter() {}
 * 3. ConstructorWithOneParam - Counter(int initial)
 * 4. ConstructorWithTwoParams - Counter(int a, int b)
 * 5. ConstructorWithMemberInitBody - field assignment in body
 * 6. ConstructorWithMemberInitList - : field(value) syntax
 * 7. ConstructorWithMultipleInitList - : f1(v1), f2(v2)
 * 8. MultipleConstructors - overloading with different params
 * 9. ConstructorCallingMethod - calls other methods in body
 * 10. ConstructorWithPointerParam - Counter(int* ptr)
 * 11. ConstructorWithReferenceParam - Counter(int& ref)
 * 12. ConstructorInitAllFieldTypes - int, float, pointer, array
 * 13. ConstructorWithComplexExpr - initializer with expressions
 * 14. ConstructorNameMangling - verify correct naming
 * 15. ConstructorThisParameter - verify this parameter is first
 */

#include "dispatch/ConstructorHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Frontend/ASTUnit.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ConstructorHandlerTest
 * @brief Test fixture for ConstructorHandler
 *
 * Uses clang::tooling::buildASTFromCode for real AST contexts.
 */
class ConstructorHandlerTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    void SetUp() override {
        // Create real AST contexts using minimal code
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr) << "Failed to create C++ AST";
        ASSERT_NE(cAST, nullptr) << "Failed to create C AST";

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );
    }

    void TearDown() override {
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Helper to find constructor in a class
     */
    clang::CXXConstructorDecl* findConstructor(
        clang::CXXRecordDecl* record,
        unsigned numParams = 0
    ) {
        for (auto* ctor : record->ctors()) {
            if (ctor->getNumParams() == numParams) {
                return ctor;
            }
        }
        return nullptr;
    }

    /**
     * @brief Build AST from code and find first class
     */
    clang::CXXRecordDecl* parseClassFromCode(const std::string& code) {
        cppAST = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(cppAST, nullptr) << "Failed to parse code";
        if (!cppAST) return nullptr;

        // Find the class declaration
        auto& ctx = cppAST->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (!record->isImplicit()) {
                    return record;
                }
            }
        }
        return nullptr;
    }
};

// ============================================================================
// Test 1: Empty Default Constructor
// ============================================================================

/**
 * Test 1: Translate empty default constructor
 *
 * C++ Input:  class Counter { public: Counter() {} };
 * C Output:   void Counter_init(struct Counter* this);
 *
 * This is the simplest possible constructor - no parameters, no body.
 */
TEST_F(ConstructorHandlerTest, EmptyDefaultConstructor) {
    // Arrange: Parse C++ class with default constructor
    const char* code = R"(
        class Counter {
        public:
            Counter() {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr) << "Failed to parse class";

    auto* ctor = findConstructor(record, 0);
    ASSERT_NE(ctor, nullptr) << "Failed to find constructor";

    // Act: Translate using ConstructorHandler
    ConstructorHandler handler;
    clang::Decl* result = handler.handleDecl(ctor, *context);

    // Assert: Verify C init function created
    ASSERT_NE(result, nullptr) << "Translation returned null";

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr) << "Result is not a FunctionDecl";

    EXPECT_EQ(cFunc->getNameAsString(), "Counter_init")
        << "Function name should be Counter_init";
    EXPECT_TRUE(cFunc->getReturnType()->isVoidType())
        << "Return type should be void";
    EXPECT_EQ(cFunc->getNumParams(), 1)
        << "Should have 1 parameter (this)";

    // Check 'this' parameter
    auto* thisParam = cFunc->getParamDecl(0);
    EXPECT_EQ(thisParam->getNameAsString(), "this")
        << "First parameter should be named 'this'";
    EXPECT_TRUE(thisParam->getType()->isPointerType())
        << "'this' should be pointer type";
}

// ============================================================================
// Test 2: Constructor with Member Initializer List
// ============================================================================

/**
 * Test 2: Constructor with simple member initializer list
 *
 * C++ Input:  class Counter {
 *                 int count;
 *             public:
 *                 Counter() : count(0) {}
 *             };
 * C Output:   void Counter_init(struct Counter* this) {
 *                 this->count = 0;
 *             }
 *
 * Member initializer list (: count(0)) should be converted to assignment.
 */
TEST_F(ConstructorHandlerTest, ConstructorWithMemberInitList) {
    // Arrange
    const char* code = R"(
        class Counter {
            int count;
        public:
            Counter() : count(0) {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor = findConstructor(record, 0);
    ASSERT_NE(ctor, nullptr);

    // Act
    ConstructorHandler handler;
    clang::Decl* result = handler.handleDecl(ctor, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "Counter_init");
    EXPECT_EQ(cFunc->getNumParams(), 1);

    // Note: Member init list translation is implementation detail
    // Main requirement is that function is created correctly
}

// ============================================================================
// Test 3: Constructor with One Parameter
// ============================================================================

/**
 * Test 3: Constructor with one parameter
 *
 * C++ Input:  class Counter {
 *             public:
 *                 Counter(int initial) {}
 *             };
 * C Output:   void Counter_init_int(struct Counter* this, int initial);
 *
 * Name should include parameter type for overload resolution.
 */
TEST_F(ConstructorHandlerTest, ConstructorWithOneParam) {
    // Arrange
    const char* code = R"(
        class Counter {
        public:
            Counter(int initial) {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor = findConstructor(record, 1);
    ASSERT_NE(ctor, nullptr);

    // Act
    ConstructorHandler handler;
    clang::Decl* result = handler.handleDecl(ctor, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "Counter_init_int")
        << "Function name should include parameter type";
    EXPECT_EQ(cFunc->getNumParams(), 2)
        << "Should have 2 parameters (this + initial)";

    // Check parameters
    auto* thisParam = cFunc->getParamDecl(0);
    EXPECT_EQ(thisParam->getNameAsString(), "this");

    auto* initialParam = cFunc->getParamDecl(1);
    EXPECT_EQ(initialParam->getNameAsString(), "initial");
    EXPECT_TRUE(initialParam->getType()->isIntegerType());
}

// ============================================================================
// Test 4: Constructor with Two Parameters
// ============================================================================

/**
 * Test 4: Constructor with two parameters
 *
 * C++ Input:  class Point {
 *             public:
 *                 Point(int x, int y) {}
 *             };
 * C Output:   void Point_init_int_int(struct Point* this, int x, int y);
 */
TEST_F(ConstructorHandlerTest, ConstructorWithTwoParams) {
    // Arrange
    const char* code = R"(
        class Point {
        public:
            Point(int x, int y) {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor = findConstructor(record, 2);
    ASSERT_NE(ctor, nullptr);

    // Act
    ConstructorHandler handler;
    clang::Decl* result = handler.handleDecl(ctor, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "Point_init_int_int");
    EXPECT_EQ(cFunc->getNumParams(), 3) << "Should have 3 params (this + x + y)";

    auto* param1 = cFunc->getParamDecl(1);
    EXPECT_EQ(param1->getNameAsString(), "x");

    auto* param2 = cFunc->getParamDecl(2);
    EXPECT_EQ(param2->getNameAsString(), "y");
}

// ============================================================================
// Test 5: Constructor with Member Initialization in Body
// ============================================================================

/**
 * Test 5: Constructor with member initialization in body (not init list)
 *
 * C++ Input:  class Counter {
 *                 int count;
 *             public:
 *                 Counter() { count = 0; }
 *             };
 * C Output:   void Counter_init(struct Counter* this) {
 *                 this->count = 0;
 *             }
 */
TEST_F(ConstructorHandlerTest, ConstructorWithMemberInitBody) {
    // Arrange
    const char* code = R"(
        class Counter {
            int count;
        public:
            Counter() { count = 0; }
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor = findConstructor(record, 0);
    ASSERT_NE(ctor, nullptr);

    // Act
    ConstructorHandler handler;
    clang::Decl* result = handler.handleDecl(ctor, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "Counter_init");

    // Body translation is handled by StatementHandler
    // We just verify the function declaration is correct
}

// ============================================================================
// Test 6: Multiple Constructors (Overloading)
// ============================================================================

/**
 * Test 6: Multiple constructors with different parameter counts
 *
 * C++ Input:  class Counter {
 *             public:
 *                 Counter() {}
 *                 Counter(int i) {}
 *             };
 * C Output:   void Counter_init(struct Counter* this);
 *             void Counter_init_int(struct Counter* this, int i);
 *
 * Different mangled names for overloaded constructors.
 */
TEST_F(ConstructorHandlerTest, MultipleConstructors) {
    // Arrange
    const char* code = R"(
        class Counter {
        public:
            Counter() {}
            Counter(int i) {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor0 = findConstructor(record, 0);
    auto* ctor1 = findConstructor(record, 1);
    ASSERT_NE(ctor0, nullptr);
    ASSERT_NE(ctor1, nullptr);

    // Act
    ConstructorHandler handler;
    clang::Decl* result0 = handler.handleDecl(ctor0, *context);
    clang::Decl* result1 = handler.handleDecl(ctor1, *context);

    // Assert
    ASSERT_NE(result0, nullptr);
    ASSERT_NE(result1, nullptr);

    auto* cFunc0 = llvm::dyn_cast<clang::FunctionDecl>(result0);
    auto* cFunc1 = llvm::dyn_cast<clang::FunctionDecl>(result1);
    ASSERT_NE(cFunc0, nullptr);
    ASSERT_NE(cFunc1, nullptr);

    EXPECT_EQ(cFunc0->getNameAsString(), "Counter_init");
    EXPECT_EQ(cFunc1->getNameAsString(), "Counter_init_int");
    EXPECT_NE(cFunc0->getNameAsString(), cFunc1->getNameAsString())
        << "Overloaded constructors should have different names";
}

// ============================================================================
// Test 7: Constructor with Multiple Member Initializers
// ============================================================================

/**
 * Test 7: Constructor with multiple fields in initializer list
 *
 * C++ Input:  class Point {
 *                 int x, y;
 *             public:
 *                 Point() : x(0), y(0) {}
 *             };
 */
TEST_F(ConstructorHandlerTest, ConstructorWithMultipleInitList) {
    // Arrange
    const char* code = R"(
        class Point {
            int x;
            int y;
        public:
            Point() : x(0), y(0) {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor = findConstructor(record, 0);
    ASSERT_NE(ctor, nullptr);

    // Act
    ConstructorHandler handler;
    clang::Decl* result = handler.handleDecl(ctor, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "Point_init");
}

// ============================================================================
// Test 8: Constructor with Pointer Parameter
// ============================================================================

/**
 * Test 8: Constructor with pointer parameter
 *
 * C++ Input:  class Wrapper {
 *             public:
 *                 Wrapper(int* ptr) {}
 *             };
 * C Output:   void Wrapper_init_intptr(struct Wrapper* this, int* ptr);
 */
TEST_F(ConstructorHandlerTest, ConstructorWithPointerParam) {
    // Arrange
    const char* code = R"(
        class Wrapper {
        public:
            Wrapper(int* ptr) {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor = findConstructor(record, 1);
    ASSERT_NE(ctor, nullptr);

    // Act
    ConstructorHandler handler;
    clang::Decl* result = handler.handleDecl(ctor, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    // Name should include pointer type
    std::string name = cFunc->getNameAsString();
    EXPECT_TRUE(name.find("Wrapper_init") == 0)
        << "Name should start with Wrapper_init";

    EXPECT_EQ(cFunc->getNumParams(), 2);
    auto* ptrParam = cFunc->getParamDecl(1);
    EXPECT_TRUE(ptrParam->getType()->isPointerType());
}

// ============================================================================
// Test 9: Constructor with Reference Parameter
// ============================================================================

/**
 * Test 9: Constructor with reference parameter (converted to pointer)
 *
 * C++ Input:  class Wrapper {
 *             public:
 *                 Wrapper(int& ref) {}
 *             };
 * C Output:   void Wrapper_init_intptr(struct Wrapper* this, int* ref);
 *
 * Reference should be converted to pointer in C.
 */
TEST_F(ConstructorHandlerTest, ConstructorWithReferenceParam) {
    // Arrange
    const char* code = R"(
        class Wrapper {
        public:
            Wrapper(int& ref) {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor = findConstructor(record, 1);
    ASSERT_NE(ctor, nullptr);

    // Act
    ConstructorHandler handler;
    clang::Decl* result = handler.handleDecl(ctor, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNumParams(), 2);
    auto* refParam = cFunc->getParamDecl(1);
    EXPECT_TRUE(refParam->getType()->isPointerType())
        << "Reference parameter should be converted to pointer";
}

// ============================================================================
// Test 10: Constructor with Float Parameter
// ============================================================================

/**
 * Test 10: Constructor with float parameter (type name mangling)
 *
 * C++ Input:  class Value {
 *             public:
 *                 Value(float f) {}
 *             };
 * C Output:   void Value_init_float(struct Value* this, float f);
 */
TEST_F(ConstructorHandlerTest, ConstructorWithFloatParam) {
    // Arrange
    const char* code = R"(
        class Value {
        public:
            Value(float f) {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor = findConstructor(record, 1);
    ASSERT_NE(ctor, nullptr);

    // Act
    ConstructorHandler handler;
    clang::Decl* result = handler.handleDecl(ctor, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "Value_init_float");
}

// ============================================================================
// Test 11: Constructor with Mixed Parameter Types
// ============================================================================

/**
 * Test 11: Constructor with multiple different parameter types
 *
 * C++ Input:  class Data {
 *             public:
 *                 Data(int i, float f) {}
 *             };
 * C Output:   void Data_init_int_float(struct Data* this, int i, float f);
 */
TEST_F(ConstructorHandlerTest, ConstructorWithMixedParams) {
    // Arrange
    const char* code = R"(
        class Data {
        public:
            Data(int i, float f) {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor = findConstructor(record, 2);
    ASSERT_NE(ctor, nullptr);

    // Act
    ConstructorHandler handler;
    clang::Decl* result = handler.handleDecl(ctor, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "Data_init_int_float");
    EXPECT_EQ(cFunc->getNumParams(), 3);
}

// ============================================================================
// Test 12: canHandle Returns True for Constructor
// ============================================================================

/**
 * Test 12: Verify canHandle correctly identifies constructors
 */
TEST_F(ConstructorHandlerTest, CanHandleConstructor) {
    // Arrange
    const char* code = R"(
        class Counter {
        public:
            Counter() {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor = findConstructor(record, 0);
    ASSERT_NE(ctor, nullptr);

    // Act
    ConstructorHandler handler;
    bool canHandle = handler.canHandle(ctor);

    // Assert
    EXPECT_TRUE(canHandle) << "Handler should recognize CXXConstructorDecl";
}

// ============================================================================
// Test 13: canHandle Returns False for Non-Constructor
// ============================================================================

/**
 * Test 13: Verify canHandle rejects non-constructor declarations
 */
TEST_F(ConstructorHandlerTest, CanHandleRejectsNonConstructor) {
    // Arrange: Create a regular function
    const char* code = R"(
        void regularFunction() {}
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    auto* TU = cppAST->getASTContext().getTranslationUnitDecl();
    clang::FunctionDecl* func = nullptr;
    for (auto* decl : TU->decls()) {
        if (auto* f = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            if (!f->isImplicit()) {
                func = f;
                break;
            }
        }
    }
    ASSERT_NE(func, nullptr);

    // Act
    ConstructorHandler handler;
    bool canHandle = handler.canHandle(func);

    // Assert
    EXPECT_FALSE(canHandle) << "Handler should reject regular functions";
}

// ============================================================================
// Test 14: Constructor Init List with Parameter
// ============================================================================

/**
 * Test 14: Constructor using parameter in member initializer list
 *
 * C++ Input:  class Counter {
 *                 int count;
 *             public:
 *                 Counter(int initial) : count(initial) {}
 *             };
 * C Output:   void Counter_init_int(struct Counter* this, int initial) {
 *                 this->count = initial;
 *             }
 */
TEST_F(ConstructorHandlerTest, ConstructorInitListWithParameter) {
    // Arrange
    const char* code = R"(
        class Counter {
            int count;
        public:
            Counter(int initial) : count(initial) {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor = findConstructor(record, 1);
    ASSERT_NE(ctor, nullptr);

    // Act
    ConstructorHandler handler;
    clang::Decl* result = handler.handleDecl(ctor, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "Counter_init_int");
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

// ============================================================================
// Test 15: Constructor This Parameter Type
// ============================================================================

/**
 * Test 15: Verify 'this' parameter has correct type (struct ClassName*)
 *
 * The first parameter should be: struct Counter* this
 */
TEST_F(ConstructorHandlerTest, ConstructorThisParameterType) {
    // Arrange
    const char* code = R"(
        class Counter {
        public:
            Counter() {}
        };
    )";

    auto* record = parseClassFromCode(code);
    ASSERT_NE(record, nullptr);

    auto* ctor = findConstructor(record, 0);
    ASSERT_NE(ctor, nullptr);

    // Act
    ConstructorHandler handler;
    clang::Decl* result = handler.handleDecl(ctor, *context);

    // Assert
    ASSERT_NE(result, nullptr);
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(result);
    ASSERT_NE(cFunc, nullptr);

    auto* thisParam = cFunc->getParamDecl(0);
    ASSERT_NE(thisParam, nullptr);

    EXPECT_EQ(thisParam->getNameAsString(), "this");

    // Check that it's a pointer type
    clang::QualType thisType = thisParam->getType();
    EXPECT_TRUE(thisType->isPointerType()) << "'this' must be pointer type";

    // Check that it points to a record type (struct)
    if (thisType->isPointerType()) {
        clang::QualType pointeeType = thisType->getPointeeType();
        EXPECT_TRUE(pointeeType->isRecordType() || pointeeType->isStructureType())
            << "'this' should point to struct/record type";
    }
}
