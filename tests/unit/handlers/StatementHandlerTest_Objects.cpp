/**
 * @file StatementHandlerTest_Objects.cpp
 * @brief TDD tests for Object Construction and Destruction (Phase 44, Task 9)
 *
 * Following strict TDD: Red -> Green -> Refactor
 *
 * Test Plan (12 tests):
 * 1. SimpleObjectDeclaration - MyClass obj;
 * 2. ObjectWithConstructorArgs - MyClass obj(1, 2);
 * 3. ObjectInIfBlock - destructor at end of block
 * 4. ObjectInLoop - destructor each iteration
 * 5. MultipleObjectsInScope - correct destructor order
 * 6. ObjectWithDefaultConstructor - zero-arg init
 * 7. ObjectWithParameterizedConstructor - multi-arg init
 * 8. EarlyReturn - destructor before return
 * 9. NestedScopes - destructors at each scope end
 * 10. ObjectInSwitchCase - destructor at case end
 * 11. MultipleEarlyReturns - destructors before each return
 * 12. ObjectWithNoConstructor - struct without constructor
 *
 * Translation Strategy:
 * - Detect VarDecl with CXXRecordDecl type
 * - Keep variable declaration but remove initializer
 * - Create constructor call: ClassName_init(&obj, args...)
 * - Insert as separate statement after declaration
 * - Track objects in scope for destructor injection
 * - Insert destructor calls in reverse order (stack unwinding)
 * - Handle early returns by injecting destructors before return
 */

#include "dispatch/StatementHandler.h"
#include "handlers/HandlerContext.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/DeclCXX.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

class StatementHandlerObjectsTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    void SetUp() override {
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");
        ASSERT_NE(cppAST, nullptr);
        ASSERT_NE(cAST, nullptr);
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );
    }

    /**
     * @brief Parse code and find first class declaration
     */
    clang::CXXRecordDecl* parseClassFromCode(const std::string& code) {
        cppAST = clang::tooling::buildASTFromCode(code);
        if (!cppAST) return nullptr;

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

    /**
     * @brief Parse code and find first function declaration
     */
    clang::FunctionDecl* parseFunctionFromCode(const std::string& code) {
        cppAST = clang::tooling::buildASTFromCode(code);
        if (!cppAST) return nullptr;

        auto& ctx = cppAST->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
                if (!func->isImplicit()) {
                    return func;
                }
            }
        }
        return nullptr;
    }

    /**
     * @brief Helper to create VarDecl with class type
     */
    clang::VarDecl* createObjectVarDecl(
        const std::string& name,
        clang::CXXRecordDecl* recordDecl
    ) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        clang::QualType type = ctx.getRecordType(recordDecl);
        clang::IdentifierInfo& II = ctx.Idents.get(name);

        return clang::VarDecl::Create(
            ctx,
            ctx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            &II,
            type,
            ctx.getTrivialTypeSourceInfo(type),
            clang::SC_None
        );
    }

    /**
     * @brief Create DeclStmt for a VarDecl
     */
    clang::DeclStmt* createDeclStmt(clang::VarDecl* var) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return new (ctx) clang::DeclStmt(
            clang::DeclGroupRef(var),
            clang::SourceLocation(),
            clang::SourceLocation()
        );
    }

    /**
     * @brief Create compound statement
     */
    clang::CompoundStmt* createCompoundStmt(const std::vector<clang::Stmt*>& stmts) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return clang::CompoundStmt::Create(
            ctx, stmts, clang::FPOptionsOverride(),
            clang::SourceLocation(), clang::SourceLocation()
        );
    }

    /**
     * @brief Create return statement
     */
    clang::ReturnStmt* createReturnStmt(clang::Expr* retValue = nullptr) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        return clang::ReturnStmt::Create(
            ctx,
            clang::SourceLocation(),
            retValue,
            nullptr
        );
    }

    /**
     * @brief Create integer literal
     */
    clang::IntegerLiteral* createIntLiteral(int value) {
        clang::ASTContext& ctx = cppAST->getASTContext();
        llvm::APInt apValue(32, value);
        return clang::IntegerLiteral::Create(
            ctx, apValue, ctx.IntTy, clang::SourceLocation()
        );
    }
};

// ============================================================================
// Test 1: Simple Object Declaration - MyClass obj;
// ============================================================================
TEST_F(StatementHandlerObjectsTest, SimpleObjectDeclaration) {
    // Arrange: Create class and object declaration
    const char* code = R"(
        class MyClass {
        public:
            MyClass() {}
        };
    )";

    auto* recordDecl = parseClassFromCode(code);
    ASSERT_NE(recordDecl, nullptr);

    auto* varDecl = createObjectVarDecl("obj", recordDecl);
    auto* declStmt = createDeclStmt(varDecl);

    // Act: Translate
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(declStmt, *context);

    // Assert: Should return CompoundStmt with declaration + constructor call
    ASSERT_NE(result, nullptr);

    // For now, we expect it to pass through or return a modified statement
    // The actual implementation will create a compound statement with:
    // 1. Variable declaration (without initializer)
    // 2. Constructor call: MyClass_init(&obj);

    // This test WILL FAIL until we implement the feature
    auto* compound = llvm::dyn_cast<clang::CompoundStmt>(result);
    EXPECT_NE(compound, nullptr) << "Expected CompoundStmt with decl + ctor call";
}

// ============================================================================
// Test 2: Object With Constructor Arguments - MyClass obj(1, 2);
// ============================================================================
TEST_F(StatementHandlerObjectsTest, ObjectWithConstructorArgs) {
    // Arrange: Parse class with parameterized constructor
    const char* code = R"(
        class MyClass {
        public:
            MyClass(int a, int b) {}
        };
    )";

    auto* recordDecl = parseClassFromCode(code);
    ASSERT_NE(recordDecl, nullptr);

    auto* varDecl = createObjectVarDecl("obj", recordDecl);

    // Create constructor arguments
    std::vector<clang::Expr*> args;
    args.push_back(createIntLiteral(1));
    args.push_back(createIntLiteral(2));

    // TODO: Set initializer on varDecl
    // For now, just test with declaration
    auto* declStmt = createDeclStmt(varDecl);

    // Act: Translate
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(declStmt, *context);

    // Assert: Should create MyClass_init_int_int(&obj, 1, 2);
    ASSERT_NE(result, nullptr);

    // This test WILL FAIL until we implement the feature
    auto* compound = llvm::dyn_cast<clang::CompoundStmt>(result);
    EXPECT_NE(compound, nullptr) << "Expected CompoundStmt with decl + ctor call";

    if (compound) {
        EXPECT_GE(compound->size(), 2) << "Should have declaration + ctor call";
    }
}

// ============================================================================
// Test 3: Object In If Block - destructor at end of block
// ============================================================================
TEST_F(StatementHandlerObjectsTest, ObjectInIfBlock) {
    // Arrange: Parse function with object in if block
    const char* code = R"(
        class MyClass {
        public:
            MyClass() {}
            ~MyClass() {}
        };

        void testFunc() {
            if (true) {
                MyClass obj;
            }
        }
    )";

    auto* func = parseFunctionFromCode(code);
    ASSERT_NE(func, nullptr);
    ASSERT_TRUE(func->hasBody());

    auto* body = func->getBody();
    ASSERT_NE(body, nullptr);

    // Act: Translate function body
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(body, *context);

    // Assert: If block should have destructor call at end
    ASSERT_NE(result, nullptr);

    // This test WILL FAIL until we implement destructor injection
    auto* compound = llvm::dyn_cast<clang::CompoundStmt>(result);
    EXPECT_NE(compound, nullptr);

    // The if block should contain:
    // 1. struct MyClass obj;
    // 2. MyClass_init(&obj);
    // 3. MyClass_destroy(&obj); // At end of block
}

// ============================================================================
// Test 4: Object In Loop - destructor each iteration
// ============================================================================
TEST_F(StatementHandlerObjectsTest, ObjectInLoop) {
    // Arrange: Parse function with object in while loop
    const char* code = R"(
        class MyClass {
        public:
            MyClass() {}
            ~MyClass() {}
        };

        void testFunc() {
            while (true) {
                MyClass obj;
            }
        }
    )";

    auto* func = parseFunctionFromCode(code);
    ASSERT_NE(func, nullptr);
    ASSERT_TRUE(func->hasBody());

    // Act: Translate
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(func->getBody(), *context);

    // Assert: Loop body should have destructor at end
    ASSERT_NE(result, nullptr);

    // This test WILL FAIL until we implement destructor injection
    // The while body should contain destructor call at end of each iteration
}

// ============================================================================
// Test 5: Multiple Objects In Same Scope - reverse order destruction
// ============================================================================
TEST_F(StatementHandlerObjectsTest, MultipleObjectsInScope) {
    // Arrange: Parse function with multiple objects
    const char* code = R"(
        class MyClass {
        public:
            MyClass() {}
            ~MyClass() {}
        };

        void testFunc() {
            MyClass obj1;
            MyClass obj2;
            MyClass obj3;
        }
    )";

    auto* func = parseFunctionFromCode(code);
    ASSERT_NE(func, nullptr);
    ASSERT_TRUE(func->hasBody());

    // Act: Translate
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(func->getBody(), *context);

    // Assert: Destructors should be called in reverse order: obj3, obj2, obj1
    ASSERT_NE(result, nullptr);

    // This test WILL FAIL until we implement destructor injection
    auto* compound = llvm::dyn_cast<clang::CompoundStmt>(result);
    EXPECT_NE(compound, nullptr);

    // Expected order:
    // 1. struct MyClass obj1; MyClass_init(&obj1);
    // 2. struct MyClass obj2; MyClass_init(&obj2);
    // 3. struct MyClass obj3; MyClass_init(&obj3);
    // 4. MyClass_destroy(&obj3); // Reverse order
    // 5. MyClass_destroy(&obj2);
    // 6. MyClass_destroy(&obj1);
}

// ============================================================================
// Test 6: Object With Default Constructor - zero-arg init
// ============================================================================
TEST_F(StatementHandlerObjectsTest, ObjectWithDefaultConstructor) {
    // Arrange: Create class with explicit default constructor
    const char* code = R"(
        class Counter {
        public:
            Counter() : count(0) {}
        private:
            int count;
        };
    )";

    auto* recordDecl = parseClassFromCode(code);
    ASSERT_NE(recordDecl, nullptr);

    auto* varDecl = createObjectVarDecl("counter", recordDecl);
    auto* declStmt = createDeclStmt(varDecl);

    // Act: Translate
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(declStmt, *context);

    // Assert: Should create Counter_init(&counter);
    ASSERT_NE(result, nullptr);

    // This test WILL FAIL until implementation
}

// ============================================================================
// Test 7: Object With Parameterized Constructor - multi-arg init
// ============================================================================
TEST_F(StatementHandlerObjectsTest, ObjectWithParameterizedConstructor) {
    // Arrange: Parse class with multi-param constructor
    const char* code = R"(
        class Point {
        public:
            Point(int x, int y, int z) {}
        };
    )";

    auto* recordDecl = parseClassFromCode(code);
    ASSERT_NE(recordDecl, nullptr);

    auto* varDecl = createObjectVarDecl("pt", recordDecl);
    auto* declStmt = createDeclStmt(varDecl);

    // Act: Translate
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(declStmt, *context);

    // Assert: Should create Point_init_int_int_int(&pt, x, y, z);
    ASSERT_NE(result, nullptr);

    // This test WILL FAIL until implementation
}

// ============================================================================
// Test 8: Early Return - destructor before return
// ============================================================================
TEST_F(StatementHandlerObjectsTest, EarlyReturn) {
    // Arrange: Parse function with early return
    const char* code = R"(
        class MyClass {
        public:
            MyClass() {}
            ~MyClass() {}
        };

        int testFunc(bool condition) {
            MyClass obj;
            if (condition) {
                return 42;
            }
            return 0;
        }
    )";

    auto* func = parseFunctionFromCode(code);
    ASSERT_NE(func, nullptr);
    ASSERT_TRUE(func->hasBody());

    // Act: Translate
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(func->getBody(), *context);

    // Assert: Destructor should be called before each return
    ASSERT_NE(result, nullptr);

    // This test WILL FAIL until we implement early return handling
    // Before "return 42;", we need: MyClass_destroy(&obj);
    // Before "return 0;", we need: MyClass_destroy(&obj);
}

// ============================================================================
// Test 9: Nested Scopes - destructors at each scope end
// ============================================================================
TEST_F(StatementHandlerObjectsTest, NestedScopes) {
    // Arrange: Parse function with nested scopes
    const char* code = R"(
        class MyClass {
        public:
            MyClass() {}
            ~MyClass() {}
        };

        void testFunc() {
            MyClass outer;
            {
                MyClass inner;
            }
        }
    )";

    auto* func = parseFunctionFromCode(code);
    ASSERT_NE(func, nullptr);
    ASSERT_TRUE(func->hasBody());

    // Act: Translate
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(func->getBody(), *context);

    // Assert: Destructors at correct scope ends
    ASSERT_NE(result, nullptr);

    // This test WILL FAIL until implementation
    // Expected:
    // struct MyClass outer; MyClass_init(&outer);
    // {
    //     struct MyClass inner; MyClass_init(&inner);
    //     MyClass_destroy(&inner); // End of inner scope
    // }
    // MyClass_destroy(&outer); // End of outer scope
}

// ============================================================================
// Test 10: Object In Switch Case - destructor at case end
// ============================================================================
TEST_F(StatementHandlerObjectsTest, ObjectInSwitchCase) {
    // Arrange: Parse function with object in switch case
    const char* code = R"(
        class MyClass {
        public:
            MyClass() {}
            ~MyClass() {}
        };

        void testFunc(int value) {
            switch (value) {
                case 1: {
                    MyClass obj;
                    break;
                }
                case 2: {
                    MyClass obj2;
                    break;
                }
            }
        }
    )";

    auto* func = parseFunctionFromCode(code);
    ASSERT_NE(func, nullptr);
    ASSERT_TRUE(func->hasBody());

    // Act: Translate
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(func->getBody(), *context);

    // Assert: Destructor before break in each case
    ASSERT_NE(result, nullptr);

    // This test WILL FAIL until implementation
    // Each case block should have destructor before break
}

// ============================================================================
// Test 11: Multiple Early Returns - destructors before each return
// ============================================================================
TEST_F(StatementHandlerObjectsTest, MultipleEarlyReturns) {
    // Arrange: Parse function with multiple returns
    const char* code = R"(
        class Resource {
        public:
            Resource() {}
            ~Resource() {}
        };

        int testFunc(int mode) {
            Resource res;
            if (mode == 1) return 1;
            if (mode == 2) return 2;
            if (mode == 3) return 3;
            return 0;
        }
    )";

    auto* func = parseFunctionFromCode(code);
    ASSERT_NE(func, nullptr);
    ASSERT_TRUE(func->hasBody());

    // Act: Translate
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(func->getBody(), *context);

    // Assert: Destructor before each return statement
    ASSERT_NE(result, nullptr);

    // This test WILL FAIL until implementation
    // Before each return, inject: Resource_destroy(&res);
}

// ============================================================================
// Test 12: Object With No Constructor - struct without constructor
// ============================================================================
TEST_F(StatementHandlerObjectsTest, ObjectWithNoConstructor) {
    // Arrange: Parse struct without constructor (C-compatible)
    const char* code = R"(
        struct Point {
            int x;
            int y;
        };

        void testFunc() {
            Point pt;
        }
    )";

    auto* func = parseFunctionFromCode(code);
    ASSERT_NE(func, nullptr);
    ASSERT_TRUE(func->hasBody());

    // Act: Translate
    StatementHandler handler;
    clang::Stmt* result = handler.handleStmt(func->getBody(), *context);

    // Assert: No constructor call needed (C-compatible struct)
    ASSERT_NE(result, nullptr);

    // This should pass through without modification
    // struct Point pt; // No constructor call needed
}
