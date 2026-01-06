/**
 * @file VtableTypedefGeneratorTest.cpp
 * @brief TDD tests for VtableTypedefGenerator
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (10 tests):
 * 1. SimpleVoidMethod - typedef for void return, no params
 * 2. MethodWithReturnValue - typedef for int return
 * 3. MethodWithParameters - typedef with multiple parameters
 * 4. ConstMethod - typedef with const this parameter
 * 5. VirtualDestructor - typedef for virtual destructor
 * 6. MultipleMethods - typedefs for all virtual methods
 * 7. InheritedVirtualMethod - typedef for inherited virtual
 * 8. OverrideMethod - typedef for override (same signature)
 * 9. PointerReturnType - typedef for method returning pointer
 * 10. ReferenceParameters - typedef for method with reference params
 */

#include "helpers/VtableTypedefGenerator.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/DeclCXX.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class VtableTypedefGeneratorTest
 * @brief Test fixture for VtableTypedefGenerator
 */
class VtableTypedefGeneratorTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<VtableTypedefGenerator> generator;

    void SetUp() override {
        // Create real AST contexts
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr) << "Failed to create C++ AST";
        ASSERT_NE(cAST, nullptr) << "Failed to create C AST";

        // Create builder and generator
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        generator = std::make_unique<VtableTypedefGenerator>(
            cAST->getASTContext(),
            *builder
        );
    }

    void TearDown() override {
        generator.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Parse C++ code and extract first virtual method
     * @param code C++ code containing a class with virtual method
     * @return First virtual CXXMethodDecl found, or nullptr
     */
    const clang::CXXMethodDecl* parseVirtualMethod(const std::string& code) {
        auto ast = clang::tooling::buildASTFromCode(code);
        if (!ast) {
            return nullptr;
        }

        const clang::CXXMethodDecl* method = nullptr;
        auto& ctx = ast->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* D : TU->decls()) {
            if (auto* CRD = llvm::dyn_cast<clang::CXXRecordDecl>(D)) {
                if (CRD->isCompleteDefinition()) {
                    for (auto* M : CRD->methods()) {
                        if (M->isVirtual()) {
                            method = M;
                            break;
                        }
                    }
                }
            }
            if (method) break;
        }

        // Keep AST alive
        cppAST = std::move(ast);
        return method;
    }

    /**
     * @brief Parse C++ code and extract all virtual methods
     * @param code C++ code containing a class with virtual methods
     * @return Vector of virtual CXXMethodDecl pointers
     */
    std::vector<const clang::CXXMethodDecl*> parseVirtualMethods(const std::string& code) {
        std::vector<const clang::CXXMethodDecl*> methods;
        auto ast = clang::tooling::buildASTFromCode(code);
        if (!ast) {
            return methods;
        }

        auto& ctx = ast->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* D : TU->decls()) {
            if (auto* CRD = llvm::dyn_cast<clang::CXXRecordDecl>(D)) {
                if (CRD->isCompleteDefinition()) {
                    for (auto* M : CRD->methods()) {
                        if (M->isVirtual()) {
                            methods.push_back(M);
                        }
                    }
                    break;
                }
            }
        }

        // Keep AST alive
        cppAST = std::move(ast);
        return methods;
    }

    /**
     * @brief Parse C++ code and extract first CXXDestructorDecl
     */
    const clang::CXXDestructorDecl* parseVirtualDestructor(const std::string& code) {
        auto ast = clang::tooling::buildASTFromCode(code);
        if (!ast) {
            return nullptr;
        }

        const clang::CXXDestructorDecl* dtor = nullptr;
        auto& ctx = ast->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* D : TU->decls()) {
            if (auto* CRD = llvm::dyn_cast<clang::CXXRecordDecl>(D)) {
                if (CRD->isCompleteDefinition()) {
                    dtor = CRD->getDestructor();
                    if (dtor && dtor->isVirtual()) {
                        break;
                    }
                }
            }
        }

        // Keep AST alive
        cppAST = std::move(ast);
        return dtor;
    }
};

// Test 1: Simple void method - typedef void (*Animal_speak_fn)(struct Animal *this);
TEST_F(VtableTypedefGeneratorTest, SimpleVoidMethod) {
    std::string code = R"(
        class Animal {
        public:
            virtual void speak();
        };
    )";

    const auto* method = parseVirtualMethod(code);
    ASSERT_NE(method, nullptr) << "Failed to parse virtual method";
    ASSERT_TRUE(method->isVirtual()) << "Method should be virtual";

    auto* typedefDecl = generator->generateTypedef(method, "Animal");
    ASSERT_NE(typedefDecl, nullptr) << "Typedef generation failed";

    // Check typedef name: Animal_speak_fn
    EXPECT_EQ(typedefDecl->getNameAsString(), "Animal_speak_fn");

    // Check underlying type is function pointer
    auto underlyingType = typedefDecl->getUnderlyingType();
    ASSERT_TRUE(underlyingType->isPointerType()) << "Typedef should be pointer type";

    auto* ptrType = underlyingType->getAs<clang::PointerType>();
    ASSERT_NE(ptrType, nullptr);
    ASSERT_TRUE(ptrType->getPointeeType()->isFunctionProtoType())
        << "Should point to function prototype";

    // Check function signature: void (struct Animal *this)
    auto* funcType = ptrType->getPointeeType()->getAs<clang::FunctionProtoType>();
    ASSERT_NE(funcType, nullptr);

    EXPECT_TRUE(funcType->getReturnType()->isVoidType()) << "Return type should be void";
    EXPECT_EQ(funcType->getNumParams(), 1u) << "Should have 1 parameter (this)";

    // Check this parameter is struct Animal*
    auto thisParamType = funcType->getParamType(0);
    ASSERT_TRUE(thisParamType->isPointerType()) << "this should be pointer";
    auto* thisPtrType = thisParamType->getAs<clang::PointerType>();
    EXPECT_TRUE(thisPtrType->getPointeeType()->isStructureType() ||
                thisPtrType->getPointeeType()->isRecordType())
        << "this should point to struct/record";
}

// Test 2: Method with return value - typedef int (*Animal_getAge_fn)(struct Animal *this);
TEST_F(VtableTypedefGeneratorTest, MethodWithReturnValue) {
    std::string code = R"(
        class Animal {
        public:
            virtual int getAge();
        };
    )";

    const auto* method = parseVirtualMethod(code);
    ASSERT_NE(method, nullptr);

    auto* typedefDecl = generator->generateTypedef(method, "Animal");
    ASSERT_NE(typedefDecl, nullptr);

    EXPECT_EQ(typedefDecl->getNameAsString(), "Animal_getAge_fn");

    auto underlyingType = typedefDecl->getUnderlyingType();
    auto* ptrType = underlyingType->getAs<clang::PointerType>();
    ASSERT_NE(ptrType, nullptr);

    auto* funcType = ptrType->getPointeeType()->getAs<clang::FunctionProtoType>();
    ASSERT_NE(funcType, nullptr);

    // Check return type is int
    EXPECT_TRUE(funcType->getReturnType()->isIntegerType()) << "Return type should be int";
    EXPECT_EQ(funcType->getNumParams(), 1u) << "Should have 1 parameter (this)";
}

// Test 3: Method with parameters - typedef void (*Animal_setAge_fn)(struct Animal *this, int age);
TEST_F(VtableTypedefGeneratorTest, MethodWithParameters) {
    std::string code = R"(
        class Animal {
        public:
            virtual void setAge(int age);
        };
    )";

    const auto* method = parseVirtualMethod(code);
    ASSERT_NE(method, nullptr);

    auto* typedefDecl = generator->generateTypedef(method, "Animal");
    ASSERT_NE(typedefDecl, nullptr);

    EXPECT_EQ(typedefDecl->getNameAsString(), "Animal_setAge_fn");

    auto underlyingType = typedefDecl->getUnderlyingType();
    auto* ptrType = underlyingType->getAs<clang::PointerType>();
    ASSERT_NE(ptrType, nullptr);

    auto* funcType = ptrType->getPointeeType()->getAs<clang::FunctionProtoType>();
    ASSERT_NE(funcType, nullptr);

    // Should have 2 parameters: this + age
    EXPECT_EQ(funcType->getNumParams(), 2u) << "Should have 2 parameters (this, age)";

    // First param is this
    auto thisParamType = funcType->getParamType(0);
    EXPECT_TRUE(thisParamType->isPointerType()) << "First param should be this pointer";

    // Second param is int age
    auto ageParamType = funcType->getParamType(1);
    EXPECT_TRUE(ageParamType->isIntegerType()) << "Second param should be int";
}

// Test 4: Const method - typedef int (*Animal_getAge_fn)(const struct Animal *this);
TEST_F(VtableTypedefGeneratorTest, ConstMethod) {
    std::string code = R"(
        class Animal {
        public:
            virtual int getAge() const;
        };
    )";

    const auto* method = parseVirtualMethod(code);
    ASSERT_NE(method, nullptr);
    ASSERT_TRUE(method->isConst()) << "Method should be const";

    auto* typedefDecl = generator->generateTypedef(method, "Animal");
    ASSERT_NE(typedefDecl, nullptr);

    auto underlyingType = typedefDecl->getUnderlyingType();
    auto* ptrType = underlyingType->getAs<clang::PointerType>();
    ASSERT_NE(ptrType, nullptr);

    auto* funcType = ptrType->getPointeeType()->getAs<clang::FunctionProtoType>();
    ASSERT_NE(funcType, nullptr);

    // Check this parameter is const
    auto thisParamType = funcType->getParamType(0);
    ASSERT_TRUE(thisParamType->isPointerType()) << "this should be pointer";

    auto* thisPtrType = thisParamType->getAs<clang::PointerType>();
    EXPECT_TRUE(thisPtrType->getPointeeType().isConstQualified())
        << "this should point to const struct";
}

// Test 5: Virtual destructor - typedef void (*Animal_destructor_fn)(struct Animal *this);
TEST_F(VtableTypedefGeneratorTest, VirtualDestructor) {
    std::string code = R"(
        class Animal {
        public:
            virtual ~Animal();
        };
    )";

    const auto* dtor = parseVirtualDestructor(code);
    ASSERT_NE(dtor, nullptr);
    ASSERT_TRUE(dtor->isVirtual()) << "Destructor should be virtual";

    auto* typedefDecl = generator->generateTypedefForDestructor(dtor, "Animal");
    ASSERT_NE(typedefDecl, nullptr);

    EXPECT_EQ(typedefDecl->getNameAsString(), "Animal_destructor_fn");

    auto underlyingType = typedefDecl->getUnderlyingType();
    auto* ptrType = underlyingType->getAs<clang::PointerType>();
    ASSERT_NE(ptrType, nullptr);

    auto* funcType = ptrType->getPointeeType()->getAs<clang::FunctionProtoType>();
    ASSERT_NE(funcType, nullptr);

    EXPECT_TRUE(funcType->getReturnType()->isVoidType()) << "Destructor returns void";
    EXPECT_EQ(funcType->getNumParams(), 1u) << "Should have 1 parameter (this)";
}

// Test 6: Multiple methods - generate typedefs for all
TEST_F(VtableTypedefGeneratorTest, MultipleMethods) {
    std::string code = R"(
        class Animal {
        public:
            virtual void speak();
            virtual int getAge() const;
            virtual void setAge(int age);
            virtual ~Animal();
        };
    )";

    auto methods = parseVirtualMethods(code);
    ASSERT_GE(methods.size(), 3u) << "Should have at least 3 virtual methods (excluding dtor)";

    std::vector<clang::TypedefDecl*> typedefs;
    for (const auto* method : methods) {
        if (!llvm::isa<clang::CXXDestructorDecl>(method)) {
            auto* td = generator->generateTypedef(method, "Animal");
            ASSERT_NE(td, nullptr) << "Typedef generation failed for method";
            typedefs.push_back(td);
        }
    }

    EXPECT_GE(typedefs.size(), 3u) << "Should generate at least 3 typedefs";

    // Check typedef names are unique
    std::set<std::string> names;
    for (const auto* td : typedefs) {
        names.insert(td->getNameAsString());
    }
    EXPECT_EQ(names.size(), typedefs.size()) << "All typedef names should be unique";
}

// Test 7: Inherited virtual method
TEST_F(VtableTypedefGeneratorTest, InheritedVirtualMethod) {
    std::string code = R"(
        class Animal {
        public:
            virtual void speak();
        };
        class Dog : public Animal {
            // Inherits speak() but doesn't override
        };
    )";

    // Parse and get the base class method
    auto ast = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(ast, nullptr);

    const clang::CXXMethodDecl* method = nullptr;
    auto& ctx = ast->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    for (auto* D : TU->decls()) {
        if (auto* CRD = llvm::dyn_cast<clang::CXXRecordDecl>(D)) {
            if (CRD->isCompleteDefinition() && CRD->getNameAsString() == "Animal") {
                for (auto* M : CRD->methods()) {
                    if (M->isVirtual() && !llvm::isa<clang::CXXDestructorDecl>(M)) {
                        method = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(method, nullptr);
    cppAST = std::move(ast);

    // Generate typedef for Dog (derived class) using Animal's method
    auto* typedefDecl = generator->generateTypedef(method, "Dog");
    ASSERT_NE(typedefDecl, nullptr);

    // Should use Dog prefix even though method is from Animal
    EXPECT_EQ(typedefDecl->getNameAsString(), "Dog_speak_fn");
}

// Test 8: Override method - should have compatible signature
TEST_F(VtableTypedefGeneratorTest, OverrideMethod) {
    std::string code = R"(
        class Animal {
        public:
            virtual void speak();
        };
        class Dog : public Animal {
        public:
            void speak() override;
        };
    )";

    auto ast = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(ast, nullptr);

    const clang::CXXMethodDecl* dogSpeak = nullptr;
    auto& ctx = ast->getASTContext();
    auto* TU = ctx.getTranslationUnitDecl();

    for (auto* D : TU->decls()) {
        if (auto* CRD = llvm::dyn_cast<clang::CXXRecordDecl>(D)) {
            if (CRD->isCompleteDefinition() && CRD->getNameAsString() == "Dog") {
                for (auto* M : CRD->methods()) {
                    if (M->getNameAsString() == "speak") {
                        dogSpeak = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_NE(dogSpeak, nullptr);
    cppAST = std::move(ast);

    auto* typedefDecl = generator->generateTypedef(dogSpeak, "Dog");
    ASSERT_NE(typedefDecl, nullptr);

    EXPECT_EQ(typedefDecl->getNameAsString(), "Dog_speak_fn");

    // Signature should match base class
    auto underlyingType = typedefDecl->getUnderlyingType();
    auto* ptrType = underlyingType->getAs<clang::PointerType>();
    ASSERT_NE(ptrType, nullptr);

    auto* funcType = ptrType->getPointeeType()->getAs<clang::FunctionProtoType>();
    ASSERT_NE(funcType, nullptr);

    EXPECT_TRUE(funcType->getReturnType()->isVoidType());
    EXPECT_EQ(funcType->getNumParams(), 1u);
}

// Test 9: Method returning pointer
TEST_F(VtableTypedefGeneratorTest, PointerReturnType) {
    std::string code = R"(
        class Animal {
        public:
            virtual Animal* clone();
        };
    )";

    const auto* method = parseVirtualMethod(code);
    ASSERT_NE(method, nullptr);

    auto* typedefDecl = generator->generateTypedef(method, "Animal");
    ASSERT_NE(typedefDecl, nullptr);

    EXPECT_EQ(typedefDecl->getNameAsString(), "Animal_clone_fn");

    auto underlyingType = typedefDecl->getUnderlyingType();
    auto* ptrType = underlyingType->getAs<clang::PointerType>();
    ASSERT_NE(ptrType, nullptr);

    auto* funcType = ptrType->getPointeeType()->getAs<clang::FunctionProtoType>();
    ASSERT_NE(funcType, nullptr);

    // Return type should be Animal* (pointer to struct)
    auto retType = funcType->getReturnType();
    EXPECT_TRUE(retType->isPointerType()) << "Return type should be pointer";
}

// Test 10: Reference parameters (should convert to pointers in C)
TEST_F(VtableTypedefGeneratorTest, ReferenceParameters) {
    std::string code = R"(
        class Animal {
        public:
            virtual void setName(const char& name);
        };
    )";

    const auto* method = parseVirtualMethod(code);
    ASSERT_NE(method, nullptr);

    auto* typedefDecl = generator->generateTypedef(method, "Animal");
    ASSERT_NE(typedefDecl, nullptr);

    auto underlyingType = typedefDecl->getUnderlyingType();
    auto* ptrType = underlyingType->getAs<clang::PointerType>();
    ASSERT_NE(ptrType, nullptr);

    auto* funcType = ptrType->getPointeeType()->getAs<clang::FunctionProtoType>();
    ASSERT_NE(funcType, nullptr);

    // Should have 2 parameters: this + name
    EXPECT_EQ(funcType->getNumParams(), 2u);

    // Second parameter should be pointer (C equivalent of reference)
    auto nameParamType = funcType->getParamType(1);
    EXPECT_TRUE(nameParamType->isPointerType())
        << "Reference parameter should become pointer in C";
}
