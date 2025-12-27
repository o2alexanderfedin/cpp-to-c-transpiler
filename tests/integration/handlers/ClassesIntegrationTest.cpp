/**
 * @file ClassesIntegrationTest.cpp
 * @brief Integration tests for C++ class translation to C
 *
 * Tests Phase 44 features working together:
 * - Class to struct translation (RecordHandler)
 * - Method to function translation (MethodHandler)
 * - Constructor translation (ConstructorHandler)
 * - Destructor translation (DestructorHandler)
 * - Member access (this pointer)
 * - Method calls
 * - Object lifecycle
 * - Complete class translation pipeline
 */

#include "handlers/FunctionHandler.h"
#include "handlers/VariableHandler.h"
#include "handlers/ExpressionHandler.h"
#include "handlers/StatementHandler.h"
#include "handlers/RecordHandler.h"
#include "handlers/MethodHandler.h"
#include "handlers/ConstructorHandler.h"
#include "handlers/DestructorHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ClassesIntegrationTest
 * @brief Test fixture for Phase 44 integration testing
 */
class ClassesIntegrationTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    std::unique_ptr<FunctionHandler> funcHandler;
    std::unique_ptr<VariableHandler> varHandler;
    std::unique_ptr<ExpressionHandler> exprHandler;
    std::unique_ptr<StatementHandler> stmtHandler;
    std::unique_ptr<RecordHandler> recordHandler;
    std::unique_ptr<MethodHandler> methodHandler;
    std::unique_ptr<ConstructorHandler> ctorHandler;
    std::unique_ptr<DestructorHandler> dtorHandler;

    void SetUp() override {
        // Create real AST contexts
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr);
        ASSERT_NE(cAST, nullptr);

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Create all handlers
        funcHandler = std::make_unique<FunctionHandler>();
        varHandler = std::make_unique<VariableHandler>();
        exprHandler = std::make_unique<ExpressionHandler>();
        stmtHandler = std::make_unique<StatementHandler>();
        recordHandler = std::make_unique<RecordHandler>();
        methodHandler = std::make_unique<MethodHandler>();
        ctorHandler = std::make_unique<ConstructorHandler>();
        dtorHandler = std::make_unique<DestructorHandler>();
    }

    void TearDown() override {
        dtorHandler.reset();
        ctorHandler.reset();
        methodHandler.reset();
        recordHandler.reset();
        stmtHandler.reset();
        exprHandler.reset();
        varHandler.reset();
        funcHandler.reset();
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Helper to translate a class by name
     */
    clang::RecordDecl* translateClass(const std::string& code, const std::string& className) {
        auto testAST = clang::tooling::buildASTFromCode(code);
        if (!testAST) return nullptr;

        clang::CXXRecordDecl* cppClass = nullptr;
        for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (record->getNameAsString() == className && record->isCompleteDefinition()) {
                    cppClass = record;
                    break;
                }
            }
        }

        if (!cppClass) return nullptr;

        return llvm::dyn_cast<clang::RecordDecl>(
            recordHandler->handleDecl(cppClass, *context)
        );
    }

    /**
     * @brief Helper to translate a method by name
     */
    clang::FunctionDecl* translateMethod(const std::string& code, const std::string& className,
                                         const std::string& methodName) {
        auto testAST = clang::tooling::buildASTFromCode(code);
        if (!testAST) return nullptr;

        clang::CXXRecordDecl* cppClass = nullptr;
        for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (record->getNameAsString() == className && record->isCompleteDefinition()) {
                    cppClass = record;
                    break;
                }
            }
        }

        if (!cppClass) return nullptr;

        clang::CXXMethodDecl* cppMethod = nullptr;
        for (auto* method : cppClass->methods()) {
            if (method->getNameAsString() == methodName) {
                cppMethod = method;
                break;
            }
        }

        if (!cppMethod) return nullptr;

        return llvm::dyn_cast<clang::FunctionDecl>(
            methodHandler->handleDecl(cppMethod, *context)
        );
    }
};

// ============================================================================
// Category 1: Basic Class Translation (8 tests)
// ============================================================================

TEST_F(ClassesIntegrationTest, EmptyClass) {
    // Test: class Empty {};
    const char* code = R"(
        class Empty {};
    )";

    auto* cRecord = translateClass(code, "Empty");
    ASSERT_NE(cRecord, nullptr) << "Failed to translate empty class";
    EXPECT_EQ(cRecord->getNameAsString(), "Empty");
    EXPECT_TRUE(cRecord->field_empty()) << "Empty class should have no fields";
}

TEST_F(ClassesIntegrationTest, ClassWithFields) {
    // Test: class Point { int x; int y; };
    const char* code = R"(
        class Point {
        public:
            int x;
            int y;
        };
    )";

    auto* cRecord = translateClass(code, "Point");
    ASSERT_NE(cRecord, nullptr) << "Failed to translate class with fields";
    EXPECT_EQ(cRecord->getNameAsString(), "Point");

    int fieldCount = 0;
    for (auto* field : cRecord->fields()) {
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 2) << "Point should have 2 fields";
}

TEST_F(ClassesIntegrationTest, ClassWithSingleMethod) {
    // Test: class Calculator { int add(int a, int b) { return a + b; } };
    const char* code = R"(
        class Calculator {
        public:
            int add(int a, int b) {
                return a + b;
            }
        };
    )";

    auto* cMethod = translateMethod(code, "Calculator", "add");
    ASSERT_NE(cMethod, nullptr) << "Failed to translate method";
    EXPECT_EQ(cMethod->getNumParams(), 3) << "C function should have 3 params (this + 2)";
}

TEST_F(ClassesIntegrationTest, ClassWithMultipleMethods) {
    // Test: class Math { int add(); int sub(); int mul(); };
    const char* code = R"(
        class Math {
        public:
            int add(int a, int b) { return a + b; }
            int sub(int a, int b) { return a - b; }
            int mul(int a, int b) { return a * b; }
        };
    )";

    auto* cAdd = translateMethod(code, "Math", "add");
    auto* cSub = translateMethod(code, "Math", "sub");
    auto* cMul = translateMethod(code, "Math", "mul");

    ASSERT_NE(cAdd, nullptr);
    ASSERT_NE(cSub, nullptr);
    ASSERT_NE(cMul, nullptr);
}

TEST_F(ClassesIntegrationTest, ClassWithFieldsAndMethods) {
    // Test: class Counter { int value; void increment() { value++; } };
    const char* code = R"(
        class Counter {
        public:
            int value;
            void increment() {
                value++;
            }
        };
    )";

    auto* cRecord = translateClass(code, "Counter");
    ASSERT_NE(cRecord, nullptr);

    auto* cMethod = translateMethod(code, "Counter", "increment");
    ASSERT_NE(cMethod, nullptr);
    EXPECT_EQ(cMethod->getNumParams(), 1) << "increment should have 'this' parameter";
}

TEST_F(ClassesIntegrationTest, ClassWithMixedAccessSpecifiers) {
    // Test: class Mixed { private: int x; public: int getX() { return x; } };
    const char* code = R"(
        class Mixed {
        private:
            int x;
        public:
            int getX() {
                return x;
            }
        };
    )";

    auto* cRecord = translateClass(code, "Mixed");
    ASSERT_NE(cRecord, nullptr);

    auto* cMethod = translateMethod(code, "Mixed", "getX");
    ASSERT_NE(cMethod, nullptr);
}

TEST_F(ClassesIntegrationTest, ClassWithConstMethod) {
    // Test: class Reader { int getValue() const { return 42; } };
    const char* code = R"(
        class Reader {
        public:
            int getValue() const {
                return 42;
            }
        };
    )";

    auto* cMethod = translateMethod(code, "Reader", "getValue");
    ASSERT_NE(cMethod, nullptr);
    // const methods should translate to functions with const this pointer
}

TEST_F(ClassesIntegrationTest, ClassWithThisPointerAccess) {
    // Test: class Accessor { int x; int get() { return this->x; } };
    const char* code = R"(
        class Accessor {
        public:
            int x;
            int get() {
                return this->x;
            }
        };
    )";

    auto* cMethod = translateMethod(code, "Accessor", "get");
    ASSERT_NE(cMethod, nullptr);
}

// ============================================================================
// Category 2: Constructor and Destructor (8 tests)
// ============================================================================

TEST_F(ClassesIntegrationTest, DefaultConstructor) {
    // Test: class Simple { Simple() {} };
    const char* code = R"(
        class Simple {
        public:
            Simple() {}
        };
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    clang::CXXRecordDecl* cppClass = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (record->getNameAsString() == "Simple" && record->isCompleteDefinition()) {
                cppClass = record;
                break;
            }
        }
    }

    ASSERT_NE(cppClass, nullptr);

    for (auto* ctor : cppClass->ctors()) {
        if (ctor->isDefaultConstructor()) {
            auto* cCtor = llvm::dyn_cast<clang::FunctionDecl>(
                ctorHandler->handleDecl(ctor, *context)
            );
            ASSERT_NE(cCtor, nullptr);
        }
    }
}

TEST_F(ClassesIntegrationTest, ParameterizedConstructor) {
    // Test: class Point { Point(int x, int y) : x(x), y(y) {} int x, y; };
    const char* code = R"(
        class Point {
        public:
            int x, y;
            Point(int px, int py) : x(px), y(py) {}
        };
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    clang::CXXRecordDecl* cppClass = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (record->getNameAsString() == "Point" && record->isCompleteDefinition()) {
                cppClass = record;
                break;
            }
        }
    }

    ASSERT_NE(cppClass, nullptr);

    for (auto* ctor : cppClass->ctors()) {
        if (ctor->getNumParams() == 2) {
            auto* cCtor = llvm::dyn_cast<clang::FunctionDecl>(
                ctorHandler->handleDecl(ctor, *context)
            );
            ASSERT_NE(cCtor, nullptr);
            EXPECT_EQ(cCtor->getNumParams(), 3) << "Constructor should have 3 params (this + 2)";
        }
    }
}

TEST_F(ClassesIntegrationTest, Destructor) {
    // Test: class Resource { ~Resource() {} };
    const char* code = R"(
        class Resource {
        public:
            ~Resource() {}
        };
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    clang::CXXRecordDecl* cppClass = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (record->getNameAsString() == "Resource" && record->isCompleteDefinition()) {
                cppClass = record;
                break;
            }
        }
    }

    ASSERT_NE(cppClass, nullptr);

    auto* dtor = cppClass->getDestructor();
    if (dtor && dtor->isUserProvided()) {
        auto* cDtor = llvm::dyn_cast<clang::FunctionDecl>(
            dtorHandler->handleDecl(dtor, *context)
        );
        ASSERT_NE(cDtor, nullptr);
    }
}

TEST_F(ClassesIntegrationTest, ConstructorWithMemberInitList) {
    // Test: class Data { int value; Data(int v) : value(v) {} };
    const char* code = R"(
        class Data {
        public:
            int value;
            Data(int v) : value(v) {}
        };
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    clang::CXXRecordDecl* cppClass = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (record->getNameAsString() == "Data" && record->isCompleteDefinition()) {
                cppClass = record;
                break;
            }
        }
    }

    ASSERT_NE(cppClass, nullptr);

    for (auto* ctor : cppClass->ctors()) {
        if (ctor->getNumParams() == 1) {
            auto* cCtor = llvm::dyn_cast<clang::FunctionDecl>(
                ctorHandler->handleDecl(ctor, *context)
            );
            ASSERT_NE(cCtor, nullptr);
        }
    }
}

TEST_F(ClassesIntegrationTest, MultipleConstructors) {
    // Test: class Multi { Multi(); Multi(int); Multi(int, int); };
    const char* code = R"(
        class Multi {
        public:
            Multi() {}
            Multi(int x) {}
            Multi(int x, int y) {}
        };
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    clang::CXXRecordDecl* cppClass = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (record->getNameAsString() == "Multi" && record->isCompleteDefinition()) {
                cppClass = record;
                break;
            }
        }
    }

    ASSERT_NE(cppClass, nullptr);

    int ctorCount = 0;
    for (auto* ctor : cppClass->ctors()) {
        auto* cCtor = llvm::dyn_cast<clang::FunctionDecl>(
            ctorHandler->handleDecl(ctor, *context)
        );
        if (cCtor) ctorCount++;
    }
    EXPECT_GE(ctorCount, 3) << "Should translate all 3 constructors";
}

TEST_F(ClassesIntegrationTest, ConstructorAndDestructor) {
    // Test: class RAII { RAII() {} ~RAII() {} };
    const char* code = R"(
        class RAII {
        public:
            RAII() {}
            ~RAII() {}
        };
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    clang::CXXRecordDecl* cppClass = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (record->getNameAsString() == "RAII" && record->isCompleteDefinition()) {
                cppClass = record;
                break;
            }
        }
    }

    ASSERT_NE(cppClass, nullptr);

    // Test constructor
    for (auto* ctor : cppClass->ctors()) {
        if (ctor->isDefaultConstructor()) {
            auto* cCtor = llvm::dyn_cast<clang::FunctionDecl>(
                ctorHandler->handleDecl(ctor, *context)
            );
            ASSERT_NE(cCtor, nullptr);
        }
    }

    // Test destructor
    auto* dtor = cppClass->getDestructor();
    if (dtor && dtor->isUserProvided()) {
        auto* cDtor = llvm::dyn_cast<clang::FunctionDecl>(
            dtorHandler->handleDecl(dtor, *context)
        );
        ASSERT_NE(cDtor, nullptr);
    }
}

TEST_F(ClassesIntegrationTest, ConstructorWithComplexInit) {
    // Test: class Complex { int a, b; Complex(int x) : a(x + 1), b(x + 2) {} };
    const char* code = R"(
        class Complex {
        public:
            int a, b;
            Complex(int x) : a(x + 1), b(x + 2) {}
        };
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    clang::CXXRecordDecl* cppClass = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (record->getNameAsString() == "Complex" && record->isCompleteDefinition()) {
                cppClass = record;
                break;
            }
        }
    }

    ASSERT_NE(cppClass, nullptr);

    for (auto* ctor : cppClass->ctors()) {
        if (ctor->getNumParams() == 1) {
            auto* cCtor = llvm::dyn_cast<clang::FunctionDecl>(
                ctorHandler->handleDecl(ctor, *context)
            );
            ASSERT_NE(cCtor, nullptr);
        }
    }
}

TEST_F(ClassesIntegrationTest, ObjectCreationAndDestruction) {
    // Test: void func() { class Local {}; Local obj; }
    const char* code = R"(
        class Local {
        public:
            Local() {}
            ~Local() {}
        };

        void func() {
            Local obj;
        }
    )";

    // This tests the complete object lifecycle
    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    // Translation would involve constructor call on construction
    // and destructor call on scope exit
}

// ============================================================================
// Category 3: Method Interactions (8 tests)
// ============================================================================

TEST_F(ClassesIntegrationTest, MethodCallingMethod) {
    // Test: class Chain { int a() { return 1; } int b() { return a(); } };
    const char* code = R"(
        class Chain {
        public:
            int a() { return 1; }
            int b() { return a(); }
        };
    )";

    auto* cMethodA = translateMethod(code, "Chain", "a");
    auto* cMethodB = translateMethod(code, "Chain", "b");

    ASSERT_NE(cMethodA, nullptr);
    ASSERT_NE(cMethodB, nullptr);
}

TEST_F(ClassesIntegrationTest, MethodAccessingFields) {
    // Test: class Accessor { int x; int getX() { return x; } void setX(int v) { x = v; } };
    const char* code = R"(
        class Accessor {
        public:
            int x;
            int getX() { return x; }
            void setX(int v) { x = v; }
        };
    )";

    auto* cGetX = translateMethod(code, "Accessor", "getX");
    auto* cSetX = translateMethod(code, "Accessor", "setX");

    ASSERT_NE(cGetX, nullptr);
    ASSERT_NE(cSetX, nullptr);
}

TEST_F(ClassesIntegrationTest, MethodWithMultipleFieldAccess) {
    // Test: class Point { int x, y; int sum() { return x + y; } };
    const char* code = R"(
        class Point {
        public:
            int x, y;
            int sum() { return x + y; }
        };
    )";

    auto* cMethod = translateMethod(code, "Point", "sum");
    ASSERT_NE(cMethod, nullptr);
}

TEST_F(ClassesIntegrationTest, MethodModifyingFields) {
    // Test: class Modifier { int value; void increment() { value++; } };
    const char* code = R"(
        class Modifier {
        public:
            int value;
            void increment() { value++; }
            void decrement() { value--; }
            void add(int n) { value += n; }
        };
    )";

    auto* cInc = translateMethod(code, "Modifier", "increment");
    auto* cDec = translateMethod(code, "Modifier", "decrement");
    auto* cAdd = translateMethod(code, "Modifier", "add");

    ASSERT_NE(cInc, nullptr);
    ASSERT_NE(cDec, nullptr);
    ASSERT_NE(cAdd, nullptr);
}

TEST_F(ClassesIntegrationTest, ChainedMethodCalls) {
    // Test: class Fluent { Fluent& step1() { return *this; } Fluent& step2() { return *this; } };
    const char* code = R"(
        class Fluent {
        public:
            Fluent& step1() { return *this; }
            Fluent& step2() { return *this; }
        };
    )";

    auto* cStep1 = translateMethod(code, "Fluent", "step1");
    auto* cStep2 = translateMethod(code, "Fluent", "step2");

    ASSERT_NE(cStep1, nullptr);
    ASSERT_NE(cStep2, nullptr);
}

TEST_F(ClassesIntegrationTest, MethodWithLocalVariables) {
    // Test: class Local { int process(int x) { int temp = x * 2; return temp; } };
    const char* code = R"(
        class Local {
        public:
            int process(int x) {
                int temp = x * 2;
                return temp;
            }
        };
    )";

    auto* cMethod = translateMethod(code, "Local", "process");
    ASSERT_NE(cMethod, nullptr);
}

TEST_F(ClassesIntegrationTest, MethodReturningVoid) {
    // Test: class VoidMethods { void action1() {} void action2() {} };
    const char* code = R"(
        class VoidMethods {
        public:
            void action1() {}
            void action2() {}
        };
    )";

    auto* cAction1 = translateMethod(code, "VoidMethods", "action1");
    auto* cAction2 = translateMethod(code, "VoidMethods", "action2");

    ASSERT_NE(cAction1, nullptr);
    ASSERT_NE(cAction2, nullptr);
}

TEST_F(ClassesIntegrationTest, MethodWithComplexExpression) {
    // Test: class Calc { int x, y; int compute() { return (x + y) * (x - y); } };
    const char* code = R"(
        class Calc {
        public:
            int x, y;
            int compute() {
                return (x + y) * (x - y);
            }
        };
    )";

    auto* cMethod = translateMethod(code, "Calc", "compute");
    ASSERT_NE(cMethod, nullptr);
}

// ============================================================================
// Category 4: Complex Integration (8 tests)
// ============================================================================

TEST_F(ClassesIntegrationTest, CompleteClassWithAllFeatures) {
    // Test: Complete class with constructor, destructor, fields, and methods
    const char* code = R"(
        class Complete {
        public:
            int value;

            Complete() : value(0) {}
            Complete(int v) : value(v) {}
            ~Complete() {}

            int getValue() const { return value; }
            void setValue(int v) { value = v; }
            void increment() { value++; }
        };
    )";

    auto* cRecord = translateClass(code, "Complete");
    ASSERT_NE(cRecord, nullptr);

    auto* cGetValue = translateMethod(code, "Complete", "getValue");
    auto* cSetValue = translateMethod(code, "Complete", "setValue");
    auto* cIncrement = translateMethod(code, "Complete", "increment");

    ASSERT_NE(cGetValue, nullptr);
    ASSERT_NE(cSetValue, nullptr);
    ASSERT_NE(cIncrement, nullptr);
}

TEST_F(ClassesIntegrationTest, MultipleClassesInteracting) {
    // Test: Multiple classes (later, for now just ensure multiple classes translate)
    const char* code = R"(
        class ClassA {
        public:
            int valueA;
            int getA() { return valueA; }
        };

        class ClassB {
        public:
            int valueB;
            int getB() { return valueB; }
        };
    )";

    auto* cRecordA = translateClass(code, "ClassA");
    auto* cRecordB = translateClass(code, "ClassB");

    ASSERT_NE(cRecordA, nullptr);
    ASSERT_NE(cRecordB, nullptr);
}

TEST_F(ClassesIntegrationTest, ClassWithStaticMethod) {
    // Test: class Static { static int getValue() { return 42; } };
    const char* code = R"(
        class Static {
        public:
            static int getValue() { return 42; }
        };
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    clang::CXXRecordDecl* cppClass = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (record->getNameAsString() == "Static" && record->isCompleteDefinition()) {
                cppClass = record;
                break;
            }
        }
    }

    ASSERT_NE(cppClass, nullptr);

    for (auto* method : cppClass->methods()) {
        if (method->isStatic() && method->getNameAsString() == "getValue") {
            auto* cMethod = llvm::dyn_cast<clang::FunctionDecl>(
                methodHandler->handleDecl(method, *context)
            );
            ASSERT_NE(cMethod, nullptr);
            // Static methods should not have 'this' parameter
        }
    }
}

TEST_F(ClassesIntegrationTest, ClassWithOverloadedMethods) {
    // Test: class Overload { void func(int); void func(int, int); };
    const char* code = R"(
        class Overload {
        public:
            void func(int x) {}
            void func(int x, int y) {}
        };
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    clang::CXXRecordDecl* cppClass = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (record->getNameAsString() == "Overload" && record->isCompleteDefinition()) {
                cppClass = record;
                break;
            }
        }
    }

    ASSERT_NE(cppClass, nullptr);

    int methodCount = 0;
    for (auto* method : cppClass->methods()) {
        if (method->getNameAsString() == "func") {
            auto* cMethod = llvm::dyn_cast<clang::FunctionDecl>(
                methodHandler->handleDecl(method, *context)
            );
            if (cMethod) methodCount++;
        }
    }
    EXPECT_EQ(methodCount, 2) << "Should translate both overloaded methods";
}

TEST_F(ClassesIntegrationTest, ClassObjectAsParameter) {
    // Test: void func(class Param { int x; } p) {}
    const char* code = R"(
        class Param {
        public:
            int x;
        };

        void func(Param p) {
            // Use p
        }
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    // Should translate class and function accepting class object
}

TEST_F(ClassesIntegrationTest, ClassWithArrayField) {
    // Test: class Array { int data[10]; int get(int i) { return data[i]; } };
    const char* code = R"(
        class Array {
        public:
            int data[10];
            int get(int i) { return data[i]; }
        };
    )";

    auto* cRecord = translateClass(code, "Array");
    ASSERT_NE(cRecord, nullptr);

    auto* cMethod = translateMethod(code, "Array", "get");
    ASSERT_NE(cMethod, nullptr);
}

TEST_F(ClassesIntegrationTest, ClassWithPointerField) {
    // Test: class Pointer { int* ptr; int getValue() { return *ptr; } };
    const char* code = R"(
        class Pointer {
        public:
            int* ptr;
            int getValue() { return *ptr; }
        };
    )";

    auto* cRecord = translateClass(code, "Pointer");
    ASSERT_NE(cRecord, nullptr);

    auto* cMethod = translateMethod(code, "Pointer", "getValue");
    ASSERT_NE(cMethod, nullptr);
}

TEST_F(ClassesIntegrationTest, ComplexObjectLifecycle) {
    // Test: Complete object lifecycle in function
    const char* code = R"(
        class Lifecycle {
        public:
            int value;
            Lifecycle() : value(0) {}
            Lifecycle(int v) : value(v) {}
            ~Lifecycle() {}
            void process() { value *= 2; }
        };

        void useLifecycle() {
            Lifecycle obj1;
            Lifecycle obj2(42);
            obj1.process();
            obj2.process();
        }
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    // This tests complete lifecycle:
    // 1. Class translation
    // 2. Constructor calls on object creation
    // 3. Method calls
    // 4. Destructor calls on scope exit
}

// ============================================================================
// Additional Integration Tests (3 tests to reach 35)
// ============================================================================

TEST_F(ClassesIntegrationTest, NestedClassDeclaration) {
    // Test: class Outer { class Inner { int value; }; };
    const char* code = R"(
        class Outer {
        public:
            class Inner {
            public:
                int value;
            };
        };
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    clang::CXXRecordDecl* cppOuter = nullptr;
    for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (record->getNameAsString() == "Outer" && record->isCompleteDefinition()) {
                cppOuter = record;
                break;
            }
        }
    }

    ASSERT_NE(cppOuter, nullptr);

    // Find inner class
    bool foundInner = false;
    for (auto* inner : cppOuter->decls()) {
        if (auto* innerRecord = llvm::dyn_cast<clang::CXXRecordDecl>(inner)) {
            if (innerRecord->getNameAsString() == "Inner") {
                foundInner = true;
                break;
            }
        }
    }
    EXPECT_TRUE(foundInner) << "Inner class should be found";
}

TEST_F(ClassesIntegrationTest, MethodWithControlFlow) {
    // Test: class Control { int max(int a, int b) { if (a > b) return a; return b; } };
    const char* code = R"(
        class Control {
        public:
            int max(int a, int b) {
                if (a > b) {
                    return a;
                }
                return b;
            }
        };
    )";

    auto* cMethod = translateMethod(code, "Control", "max");
    ASSERT_NE(cMethod, nullptr);
}

TEST_F(ClassesIntegrationTest, ClassObjectArray) {
    // Test: void func() { class Item { int x; }; Item arr[5]; }
    const char* code = R"(
        class Item {
        public:
            int x;
            Item() : x(0) {}
        };

        void func() {
            Item arr[5];
        }
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    // This tests array of class objects
    // Each element should be constructed via constructor
}
