/**
 * @file RecordHandlerTest_Vtable.cpp
 * @brief TDD tests for RecordHandler vtable struct generation (Phase 45 Task 2)
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan:
 * 1. SingleVirtualMethod - Class with one virtual method
 * 2. MultipleVirtualMethods - Class with multiple virtual methods
 * 3. VirtualDestructor - Class with virtual destructor
 * 4. InheritedVtable - Derived class vtable compatible with base
 * 5. PureVirtualMethod - Abstract class with pure virtual method
 * 6. MixedVirtualNonVirtual - Only virtual methods in vtable
 * 7. ConstVirtualMethod - Virtual const methods
 * 8. OverridePreservesSlotOrder - Override preserves vtable slot order
 * 9. VtableComplexParameterTypes - Virtual methods with complex parameters
 * 10. VtableReturnTypes - Virtual methods with various return types
 * 11. EmptyVtable - Class without virtual methods (no vtable generated)
 * 12. MultipleOverridesInChain - Multiple overrides in inheritance chain
 *
 * Vtable Struct Pattern:
 * C++: class Shape { virtual ~Shape(); virtual double area() const = 0; };
 * C:   struct Shape_vtable {
 *          void (*destructor)(struct Shape *this);
 *          double (*area)(const struct Shape *this);
 *      };
 */

#include "handlers/RecordHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/DeclCXX.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class RecordHandlerVtableTest
 * @brief Test fixture for RecordHandler vtable struct generation
 */
class RecordHandlerVtableTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;
    std::unique_ptr<RecordHandler> handler;

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

        // Create handler
        handler = std::make_unique<RecordHandler>();
    }

    void TearDown() override {
        handler.reset();
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Build AST from code and return the first CXXRecordDecl
     */
    const clang::CXXRecordDecl* getCXXRecordDeclFromCode(const std::string& code) {
        cppAST = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(cppAST, nullptr) << "Failed to parse code: " << code;

        if (!cppAST) return nullptr;

        // Recreate builder and context with new AST
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Find the first CXXRecordDecl
        auto& ctx = cppAST->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                // Skip implicit declarations
                if (!cxxRecord->isImplicit()) {
                    return cxxRecord;
                }
            }
        }

        return nullptr;
    }

    /**
     * @brief Find a RecordDecl by name in the C AST TranslationUnit
     */
    clang::RecordDecl* findRecordByName(const std::string& name) {
        auto& cCtx = cAST->getASTContext();
        auto* TU = cCtx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* record = llvm::dyn_cast<clang::RecordDecl>(decl)) {
                if (record->getNameAsString() == name) {
                    return record;
                }
            }
        }
        return nullptr;
    }

    /**
     * @brief Verify that a vtable struct exists with expected structure
     */
    void verifyVtableStruct(
        const std::string& className,
        size_t expectedFunctionPointerCount
    ) {
        std::string vtableName = className + "_vtable";
        auto* vtableStruct = findRecordByName(vtableName);

        ASSERT_NE(vtableStruct, nullptr)
            << "Vtable struct '" << vtableName << "' not found";
        EXPECT_TRUE(vtableStruct->isStruct())
            << "Vtable should be a struct";
        EXPECT_TRUE(vtableStruct->isCompleteDefinition())
            << "Vtable struct should be complete definition";

        // Count function pointer fields
        size_t fieldCount = 0;
        for (auto* field : vtableStruct->fields()) {
            EXPECT_TRUE(field->getType()->isPointerType())
                << "Vtable field '" << field->getNameAsString()
                << "' should be a pointer (function pointer)";
            fieldCount++;
        }
        EXPECT_EQ(fieldCount, expectedFunctionPointerCount)
            << "Vtable should have " << expectedFunctionPointerCount
            << " function pointers";
    }

    /**
     * @brief Verify a specific function pointer field in vtable struct
     */
    void verifyVtableFunctionPointer(
        const std::string& vtableName,
        const std::string& functionName,
        size_t paramCount
    ) {
        auto* vtableStruct = findRecordByName(vtableName);
        ASSERT_NE(vtableStruct, nullptr) << "Vtable struct not found";

        // Find the field
        clang::FieldDecl* foundField = nullptr;
        for (auto* field : vtableStruct->fields()) {
            if (field->getNameAsString() == functionName) {
                foundField = field;
                break;
            }
        }

        ASSERT_NE(foundField, nullptr)
            << "Function pointer '" << functionName << "' not found in vtable";

        // Verify it's a pointer type
        EXPECT_TRUE(foundField->getType()->isPointerType())
            << "Function pointer should be pointer type";

        // For function pointers, we expect FunctionProtoType
        if (auto* ptrType = foundField->getType()->getAs<clang::PointerType>()) {
            auto pointeeType = ptrType->getPointeeType();
            if (auto* funcType = pointeeType->getAs<clang::FunctionProtoType>()) {
                EXPECT_EQ(funcType->getNumParams(), paramCount)
                    << "Function pointer should have " << paramCount << " parameters";
            }
        }
    }
};

// =============================================================================
// Test 1: Single Virtual Method
// =============================================================================

/**
 * Test 1: Class with single virtual method
 * C++: class Base { virtual void foo(); };
 * C:   struct Base_vtable { void (*foo)(struct Base *this); };
 */
TEST_F(RecordHandlerVtableTest, SingleVirtualMethod) {
    const char* code = R"(
        class Base {
        public:
            virtual void foo();
        };
    )";

    const auto* cppRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(cppRecord->isPolymorphic()) << "Base should be polymorphic";

    // Translate the class (should also generate vtable struct)
    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );
    ASSERT_NE(cRecord, nullptr);

    // Verify vtable struct was generated
    verifyVtableStruct("Base", 1);

    // Verify the function pointer
    verifyVtableFunctionPointer("Base_vtable", "foo", 1); // 1 param: this
}

// =============================================================================
// Test 2: Multiple Virtual Methods
// =============================================================================

/**
 * Test 2: Class with multiple virtual methods
 * C++: class Shape { virtual void draw(); virtual double area(); virtual int getID(); };
 * C:   struct Shape_vtable {
 *          void (*draw)(struct Shape *this);
 *          double (*area)(struct Shape *this);
 *          int (*getID)(struct Shape *this);
 *      };
 */
TEST_F(RecordHandlerVtableTest, MultipleVirtualMethods) {
    const char* code = R"(
        class Shape {
        public:
            virtual void draw();
            virtual double area();
            virtual int getID();
        };
    )";

    const auto* cppRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(cppRecord->isPolymorphic());

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );
    ASSERT_NE(cRecord, nullptr);

    // Verify vtable struct with 3 function pointers
    verifyVtableStruct("Shape", 3);

    // Verify each function pointer
    verifyVtableFunctionPointer("Shape_vtable", "draw", 1);
    verifyVtableFunctionPointer("Shape_vtable", "area", 1);
    verifyVtableFunctionPointer("Shape_vtable", "getID", 1);
}

// =============================================================================
// Test 3: Virtual Destructor
// =============================================================================

/**
 * Test 3: Class with virtual destructor
 * C++: class Base { virtual ~Base(); virtual void foo(); };
 * C:   struct Base_vtable {
 *          void (*destructor)(struct Base *this);
 *          void (*foo)(struct Base *this);
 *      };
 *
 * Note: Destructor should be first in vtable
 */
TEST_F(RecordHandlerVtableTest, VirtualDestructor) {
    const char* code = R"(
        class Base {
        public:
            virtual ~Base();
            virtual void foo();
        };
    )";

    const auto* cppRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(cppRecord->isPolymorphic());

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );
    ASSERT_NE(cRecord, nullptr);

    // Verify vtable struct: destructor + foo = 2 function pointers
    verifyVtableStruct("Base", 2);

    // Verify destructor is present
    auto* vtableStruct = findRecordByName("Base_vtable");
    ASSERT_NE(vtableStruct, nullptr);

    // First field should be destructor
    auto it = vtableStruct->field_begin();
    ASSERT_NE(it, vtableStruct->field_end());
    EXPECT_EQ((*it)->getNameAsString(), "destructor")
        << "First vtable entry should be destructor";

    // Second field should be foo
    ++it;
    ASSERT_NE(it, vtableStruct->field_end());
    EXPECT_EQ((*it)->getNameAsString(), "foo");
}

// =============================================================================
// Test 4: Inherited Vtable
// =============================================================================

/**
 * Test 4: Derived class vtable compatible with base
 * C++: class Base { virtual void foo(); };
 *      class Derived : public Base { virtual void foo(); virtual void bar(); };
 * C:   struct Base_vtable { void (*foo)(struct Base *this); };
 *      struct Derived_vtable {
 *          void (*foo)(struct Derived *this);
 *          void (*bar)(struct Derived *this);
 *      };
 *
 * Note: Derived vtable should have foo in same position as Base vtable
 */
TEST_F(RecordHandlerVtableTest, InheritedVtable) {
    const char* code = R"(
        class Base {
        public:
            virtual void foo();
        };

        class Derived : public Base {
        public:
            virtual void foo() override;
            virtual void bar();
        };
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    // Recreate builder and context
    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    const clang::CXXRecordDecl* cppBase = nullptr;
    const clang::CXXRecordDecl* cppDerived = nullptr;

    for (auto* decl : TU->decls()) {
        if (auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (cxxRecord->isImplicit()) continue;
            std::string name = cxxRecord->getNameAsString();
            if (name == "Base") {
                cppBase = cxxRecord;
            } else if (name == "Derived") {
                cppDerived = cxxRecord;
            }
        }
    }

    ASSERT_NE(cppBase, nullptr);
    ASSERT_NE(cppDerived, nullptr);
    EXPECT_TRUE(cppBase->isPolymorphic());
    EXPECT_TRUE(cppDerived->isPolymorphic());

    // Translate base class first
    auto* cBase = handler->handleDecl(cppBase, *context);
    ASSERT_NE(cBase, nullptr);

    // Translate derived class
    auto* cDerived = handler->handleDecl(cppDerived, *context);
    ASSERT_NE(cDerived, nullptr);

    // Verify base vtable
    verifyVtableStruct("Base", 1);

    // Verify derived vtable (should have foo + bar = 2)
    verifyVtableStruct("Derived", 2);

    // Verify slot order: foo should be first in both vtables
    auto* baseVtable = findRecordByName("Base_vtable");
    auto* derivedVtable = findRecordByName("Derived_vtable");

    ASSERT_NE(baseVtable, nullptr);
    ASSERT_NE(derivedVtable, nullptr);

    auto baseIt = baseVtable->field_begin();
    auto derivedIt = derivedVtable->field_begin();

    EXPECT_EQ((*baseIt)->getNameAsString(), "foo")
        << "Base vtable first entry should be foo";
    EXPECT_EQ((*derivedIt)->getNameAsString(), "foo")
        << "Derived vtable first entry should be foo (preserving slot order)";

    ++derivedIt;
    EXPECT_EQ((*derivedIt)->getNameAsString(), "bar")
        << "Derived vtable second entry should be bar";
}

// =============================================================================
// Test 5: Pure Virtual Method
// =============================================================================

/**
 * Test 5: Abstract class with pure virtual method
 * C++: class Shape { virtual double area() const = 0; };
 * C:   struct Shape_vtable { double (*area)(const struct Shape *this); };
 */
TEST_F(RecordHandlerVtableTest, PureVirtualMethod) {
    const char* code = R"(
        class Shape {
        public:
            virtual double area() const = 0;
        };
    )";

    const auto* cppRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(cppRecord->isPolymorphic());
    EXPECT_TRUE(cppRecord->isAbstract()) << "Shape should be abstract";

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );
    ASSERT_NE(cRecord, nullptr);

    // Pure virtual methods should still be in vtable
    verifyVtableStruct("Shape", 1);
    verifyVtableFunctionPointer("Shape_vtable", "area", 1);
}

// =============================================================================
// Test 6: Mixed Virtual/Non-Virtual
// =============================================================================

/**
 * Test 6: Class with both virtual and non-virtual methods
 * C++: class Mixed {
 *          void regular();
 *          virtual void virt();
 *          int compute();
 *      };
 * C:   struct Mixed_vtable { void (*virt)(struct Mixed *this); };
 *
 * Note: Only virtual methods in vtable
 */
TEST_F(RecordHandlerVtableTest, MixedVirtualNonVirtual) {
    const char* code = R"(
        class Mixed {
        public:
            void regular();
            virtual void virt();
            int compute();
        };
    )";

    const auto* cppRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(cppRecord->isPolymorphic());

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );
    ASSERT_NE(cRecord, nullptr);

    // Only 1 virtual method in vtable
    verifyVtableStruct("Mixed", 1);
    verifyVtableFunctionPointer("Mixed_vtable", "virt", 1);

    // Verify that regular and compute are NOT in vtable
    auto* vtableStruct = findRecordByName("Mixed_vtable");
    ASSERT_NE(vtableStruct, nullptr);

    for (auto* field : vtableStruct->fields()) {
        EXPECT_NE(field->getNameAsString(), "regular")
            << "Non-virtual method should not be in vtable";
        EXPECT_NE(field->getNameAsString(), "compute")
            << "Non-virtual method should not be in vtable";
    }
}

// =============================================================================
// Test 7: Const Virtual Method
// =============================================================================

/**
 * Test 7: Virtual const methods
 * C++: class Container {
 *          virtual int size() const;
 *          virtual bool empty() const;
 *      };
 * C:   struct Container_vtable {
 *          int (*size)(const struct Container *this);
 *          _Bool (*empty)(const struct Container *this);
 *      };
 */
TEST_F(RecordHandlerVtableTest, ConstVirtualMethod) {
    const char* code = R"(
        class Container {
        public:
            virtual int size() const;
            virtual bool empty() const;
        };
    )";

    const auto* cppRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(cppRecord->isPolymorphic());

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );
    ASSERT_NE(cRecord, nullptr);

    verifyVtableStruct("Container", 2);
    verifyVtableFunctionPointer("Container_vtable", "size", 1);
    verifyVtableFunctionPointer("Container_vtable", "empty", 1);

    // Verify const in function pointer signature
    auto* vtableStruct = findRecordByName("Container_vtable");
    ASSERT_NE(vtableStruct, nullptr);

    for (auto* field : vtableStruct->fields()) {
        if (auto* ptrType = field->getType()->getAs<clang::PointerType>()) {
            auto pointeeType = ptrType->getPointeeType();
            if (auto* funcType = pointeeType->getAs<clang::FunctionProtoType>()) {
                // First parameter should be const struct Container*
                if (funcType->getNumParams() > 0) {
                    auto paramType = funcType->getParamType(0);
                    if (auto* paramPtrType = paramType->getAs<clang::PointerType>()) {
                        EXPECT_TRUE(paramPtrType->getPointeeType().isConstQualified())
                            << "Const virtual method should have const this parameter";
                    }
                }
            }
        }
    }
}

// =============================================================================
// Test 8: Override Preserves Slot Order
// =============================================================================

/**
 * Test 8: Override preserves slot order
 * C++: class Base { virtual void a(); virtual void b(); };
 *      class Derived : public Base { virtual void b() override; };
 * C:   struct Base_vtable { void (*a)(...); void (*b)(...); };
 *      struct Derived_vtable { void (*a)(...); void (*b)(...); };
 *
 * Note: Derived vtable has same slot order even though only b is overridden
 */
TEST_F(RecordHandlerVtableTest, OverridePreservesSlotOrder) {
    const char* code = R"(
        class Base {
        public:
            virtual void a();
            virtual void b();
        };

        class Derived : public Base {
        public:
            virtual void b() override;
        };
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    const clang::CXXRecordDecl* cppBase = nullptr;
    const clang::CXXRecordDecl* cppDerived = nullptr;

    for (auto* decl : TU->decls()) {
        if (auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (cxxRecord->isImplicit()) continue;
            std::string name = cxxRecord->getNameAsString();
            if (name == "Base") cppBase = cxxRecord;
            else if (name == "Derived") cppDerived = cxxRecord;
        }
    }

    ASSERT_NE(cppBase, nullptr);
    ASSERT_NE(cppDerived, nullptr);

    handler->handleDecl(cppBase, *context);
    handler->handleDecl(cppDerived, *context);

    // Both should have 2 function pointers
    verifyVtableStruct("Base", 2);
    verifyVtableStruct("Derived", 2);

    // Verify slot order matches
    auto* baseVtable = findRecordByName("Base_vtable");
    auto* derivedVtable = findRecordByName("Derived_vtable");

    auto baseIt = baseVtable->field_begin();
    auto derivedIt = derivedVtable->field_begin();

    EXPECT_EQ((*baseIt)->getNameAsString(), "a");
    EXPECT_EQ((*derivedIt)->getNameAsString(), "a");

    ++baseIt;
    ++derivedIt;

    EXPECT_EQ((*baseIt)->getNameAsString(), "b");
    EXPECT_EQ((*derivedIt)->getNameAsString(), "b");
}

// =============================================================================
// Test 9: Vtable with Complex Parameter Types
// =============================================================================

/**
 * Test 9: Virtual methods with complex parameter types
 * C++: class Processor {
 *          virtual void process(int* data, int size);
 *          virtual int transform(const char* input, char* output);
 *      };
 * C:   struct Processor_vtable {
 *          void (*process)(struct Processor *this, int* data, int size);
 *          int (*transform)(struct Processor *this, const char* input, char* output);
 *      };
 */
TEST_F(RecordHandlerVtableTest, VtableComplexParameterTypes) {
    const char* code = R"(
        class Processor {
        public:
            virtual void process(int* data, int size);
            virtual int transform(const char* input, char* output);
        };
    )";

    const auto* cppRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(cppRecord->isPolymorphic());

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );
    ASSERT_NE(cRecord, nullptr);

    verifyVtableStruct("Processor", 2);

    // process: this + 2 params = 3 total
    verifyVtableFunctionPointer("Processor_vtable", "process", 3);

    // transform: this + 2 params = 3 total
    verifyVtableFunctionPointer("Processor_vtable", "transform", 3);
}

// =============================================================================
// Test 10: Vtable with Return Types
// =============================================================================

/**
 * Test 10: Virtual methods with various return types
 * C++: class Calculator {
 *          virtual int add(int a, int b);
 *          virtual double divide(double a, double b);
 *          virtual bool isValid();
 *      };
 * C:   struct Calculator_vtable {
 *          int (*add)(struct Calculator *this, int a, int b);
 *          double (*divide)(struct Calculator *this, double a, double b);
 *          _Bool (*isValid)(struct Calculator *this);
 *      };
 */
TEST_F(RecordHandlerVtableTest, VtableReturnTypes) {
    const char* code = R"(
        class Calculator {
        public:
            virtual int add(int a, int b);
            virtual double divide(double a, double b);
            virtual bool isValid();
        };
    )";

    const auto* cppRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_TRUE(cppRecord->isPolymorphic());

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );
    ASSERT_NE(cRecord, nullptr);

    verifyVtableStruct("Calculator", 3);

    // Verify parameter counts
    verifyVtableFunctionPointer("Calculator_vtable", "add", 3); // this + a + b
    verifyVtableFunctionPointer("Calculator_vtable", "divide", 3); // this + a + b
    verifyVtableFunctionPointer("Calculator_vtable", "isValid", 1); // this only

    // Verify return types are correctly represented
    auto* vtableStruct = findRecordByName("Calculator_vtable");
    ASSERT_NE(vtableStruct, nullptr);

    for (auto* field : vtableStruct->fields()) {
        std::string name = field->getNameAsString();
        if (auto* ptrType = field->getType()->getAs<clang::PointerType>()) {
            auto pointeeType = ptrType->getPointeeType();
            if (auto* funcType = pointeeType->getAs<clang::FunctionProtoType>()) {
                auto returnType = funcType->getReturnType();

                if (name == "add") {
                    EXPECT_TRUE(returnType->isIntegerType())
                        << "add should return int";
                } else if (name == "divide") {
                    EXPECT_TRUE(returnType->isFloatingType())
                        << "divide should return double";
                } else if (name == "isValid") {
                    EXPECT_TRUE(returnType->isBooleanType() || returnType->isIntegerType())
                        << "isValid should return bool";
                }
            }
        }
    }
}

// =============================================================================
// Test 11: Empty Vtable (No Virtual Methods)
// =============================================================================

/**
 * Test 11: Class without virtual methods (no vtable generated)
 * C++: class Plain { void foo(); int x; };
 * C:   struct Plain { int x; }; // NO vtable struct
 */
TEST_F(RecordHandlerVtableTest, EmptyVtable) {
    const char* code = R"(
        class Plain {
        public:
            void foo();
            int x;
        };
    )";

    const auto* cppRecord = getCXXRecordDeclFromCode(code);
    ASSERT_NE(cppRecord, nullptr);
    EXPECT_FALSE(cppRecord->isPolymorphic()) << "Plain should not be polymorphic";

    auto* cRecord = llvm::cast<clang::RecordDecl>(
        handler->handleDecl(cppRecord, *context)
    );
    ASSERT_NE(cRecord, nullptr);

    // NO vtable struct should be generated
    auto* vtableStruct = findRecordByName("Plain_vtable");
    EXPECT_EQ(vtableStruct, nullptr)
        << "Non-polymorphic class should not have vtable struct";
}

// =============================================================================
// Test 12: Multiple Overrides in Inheritance Chain
// =============================================================================

/**
 * Test 12: Multiple overrides in inheritance chain
 * C++: class A { virtual void foo(); };
 *      class B : public A { virtual void foo() override; virtual void bar(); };
 *      class C : public B { virtual void foo() override; };
 * C:   struct A_vtable { void (*foo)(struct A *this); };
 *      struct B_vtable { void (*foo)(struct B *this); void (*bar)(struct B *this); };
 *      struct C_vtable { void (*foo)(struct C *this); void (*bar)(struct C *this); };
 *
 * Note: C inherits bar from B, so it should be in C's vtable
 */
TEST_F(RecordHandlerVtableTest, MultipleOverridesInChain) {
    const char* code = R"(
        class A {
        public:
            virtual void foo();
        };

        class B : public A {
        public:
            virtual void foo() override;
            virtual void bar();
        };

        class C : public B {
        public:
            virtual void foo() override;
        };
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    context = std::make_unique<HandlerContext>(
        cppAST->getASTContext(),
        cAST->getASTContext(),
        *builder
    );

    auto& ctx = cppAST->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    const clang::CXXRecordDecl* cppA = nullptr;
    const clang::CXXRecordDecl* cppB = nullptr;
    const clang::CXXRecordDecl* cppC = nullptr;

    for (auto* decl : TU->decls()) {
        if (auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (cxxRecord->isImplicit()) continue;
            std::string name = cxxRecord->getNameAsString();
            if (name == "A") cppA = cxxRecord;
            else if (name == "B") cppB = cxxRecord;
            else if (name == "C") cppC = cxxRecord;
        }
    }

    ASSERT_NE(cppA, nullptr);
    ASSERT_NE(cppB, nullptr);
    ASSERT_NE(cppC, nullptr);

    // Translate in order
    handler->handleDecl(cppA, *context);
    handler->handleDecl(cppB, *context);
    handler->handleDecl(cppC, *context);

    // Verify vtable structures
    verifyVtableStruct("A", 1); // foo
    verifyVtableStruct("B", 2); // foo, bar
    verifyVtableStruct("C", 2); // foo, bar (inherited)

    // Verify slot order in C's vtable
    auto* cVtable = findRecordByName("C_vtable");
    ASSERT_NE(cVtable, nullptr);

    auto it = cVtable->field_begin();
    EXPECT_EQ((*it)->getNameAsString(), "foo")
        << "C vtable first entry should be foo";
    ++it;
    EXPECT_EQ((*it)->getNameAsString(), "bar")
        << "C vtable second entry should be bar (inherited from B)";
}
