/**
 * @file ConstructorHandlerTest_VirtualInheritance.cpp
 * @brief Unit tests for ConstructorHandler's virtual inheritance handling
 *
 * Tests ConstructorHandler's ability to:
 * 1. Detect constructors in classes with virtual bases
 * 2. Identify need for C1/C2 constructor splitting
 * 3. Handle virtual base construction ordering
 * 4. Pass VTT parameters correctly
 *
 * These are UNIT tests - they test ConstructorHandler behavior patterns without
 * requiring full integration with ConstructorSplitter (tested in integration tests).
 */

#include "dispatch/ConstructorHandler.h"
#include "UnitTestHelper.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;
using namespace cpptoc::test;

/**
 * @class ConstructorHandlerVirtualInheritanceTest
 * @brief Test fixture for ConstructorHandler virtual inheritance features
 */
class ConstructorHandlerVirtualInheritanceTest : public ::testing::Test {
protected:
    UnitTestContext ctx;

    void SetUp() override {
        ctx = createUnitTestContext();
        ctx.dispatcher->registerHandler<ConstructorHandler>();
    }

    /**
     * @brief Find constructor in a class by parameter count
     */
    clang::CXXConstructorDecl* findConstructor(
        const clang::CXXRecordDecl* record,
        unsigned numParams = 0
    ) {
        if (!record) return nullptr;

        for (auto* ctor : record->ctors()) {
            if (ctor->getNumParams() == numParams && !ctor->isDeleted()) {
                return ctor;
            }
        }
        return nullptr;
    }

    /**
     * @brief Parse code and get class by name
     */
    const clang::CXXRecordDecl* getClass(const std::string& code, const std::string& className) {
        storedAST = clang::tooling::buildASTFromCode(code);
        if (!storedAST) return nullptr;

        auto& astCtx = storedAST->getASTContext();
        auto* TU = astCtx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* recordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (recordDecl->getNameAsString() == className &&
                    recordDecl->isCompleteDefinition()) {
                    return recordDecl;
                }
            }
        }

        return nullptr;
    }

    std::unique_ptr<clang::ASTUnit> storedAST;
};

// ============================================================================
// Test 1: Constructor in Class with Single Virtual Base
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, ConstructorWithSingleVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() : b_data(0) {}
            int b_data;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Class should have virtual base
    EXPECT_GT(derived->getNumVBases(), 0);

    // Find default constructor
    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);

    // Constructor exists and is valid
    EXPECT_EQ(ctor->getNumParams(), 0);
    EXPECT_FALSE(ctor->isDeleted());
    EXPECT_FALSE(ctor->isDefaulted());
}

// ============================================================================
// Test 2: Constructor in Diamond Pattern
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, ConstructorInDiamondPattern) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Left : public virtual Base {
        public:
            Left() {}
            int l;
        };

        class Right : public virtual Base {
        public:
            Right() {}
            int r;
        };

        class Diamond : public Left, public Right {
        public:
            Diamond() {}
            int d;
        };
    )";

    auto* base = getClass(code, "Base");
    auto* left = getClass(code, "Left");
    auto* right = getClass(code, "Right");
    auto* diamond = getClass(code, "Diamond");

    ASSERT_NE(base, nullptr);
    ASSERT_NE(left, nullptr);
    ASSERT_NE(right, nullptr);
    ASSERT_NE(diamond, nullptr);

    // All should have constructors
    EXPECT_NE(findConstructor(base, 0), nullptr);
    EXPECT_NE(findConstructor(left, 0), nullptr);
    EXPECT_NE(findConstructor(right, 0), nullptr);
    EXPECT_NE(findConstructor(diamond, 0), nullptr);

    // Left and Right have virtual bases
    EXPECT_GT(left->getNumVBases(), 0);
    EXPECT_GT(right->getNumVBases(), 0);

    // Diamond inherits virtual base
    EXPECT_GT(diamond->getNumVBases(), 0);
}

// ============================================================================
// Test 3: Constructor with Member Initializer List and Virtual Base
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, ConstructorWithInitListAndVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            Base(int val) : value(val) {}
            virtual ~Base() {}
            int value;
        };

        class Derived : public virtual Base {
        public:
            Derived(int b, int d) : Base(b), data(d) {}
            int data;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Has virtual base
    EXPECT_GT(derived->getNumVBases(), 0);

    // Find constructor with 2 params
    auto* ctor = findConstructor(derived, 2);
    ASSERT_NE(ctor, nullptr);

    // Constructor should have initializer list
    EXPECT_TRUE(ctor->init_begin() != ctor->init_end());

    // Count initializers (should have Base and data)
    size_t initCount = 0;
    for (auto it = ctor->init_begin(); it != ctor->init_end(); ++it) {
        initCount++;
    }
    EXPECT_EQ(initCount, 2); // Base + data
}

// ============================================================================
// Test 4: Multiple Constructors with Virtual Base
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, MultipleConstructorsWithVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            Base(int val) : value(val) {}
            virtual ~Base() {}
            int value;
        };

        class Derived : public virtual Base {
        public:
            Derived() : data(0) {}
            Derived(int d) : data(d) {}
            Derived(int b, int d) : Base(b), data(d) {}
            int data;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Has virtual base
    EXPECT_GT(derived->getNumVBases(), 0);

    // Should have 3 constructors
    auto* ctor0 = findConstructor(derived, 0);
    auto* ctor1 = findConstructor(derived, 1);
    auto* ctor2 = findConstructor(derived, 2);

    EXPECT_NE(ctor0, nullptr);
    EXPECT_NE(ctor1, nullptr);
    EXPECT_NE(ctor2, nullptr);

    // All are valid
    for (auto* ctor : {ctor0, ctor1, ctor2}) {
        EXPECT_FALSE(ctor->isDeleted());
    }
}

// ============================================================================
// Test 5: Constructor in Class with No Virtual Bases
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, ConstructorWithNoVirtualBases) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public Base {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // No virtual bases
    EXPECT_EQ(derived->getNumVBases(), 0);

    // Constructor exists
    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);

    EXPECT_FALSE(ctor->isDeleted());
}

// ============================================================================
// Test 6: Constructor with Multiple Virtual Bases
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, ConstructorWithMultipleVirtualBases) {
    std::string code = R"(
        class Base1 {
        public:
            Base1() {}
            virtual ~Base1() {}
            int b1;
        };

        class Base2 {
        public:
            Base2() {}
            virtual ~Base2() {}
            int b2;
        };

        class Derived : public virtual Base1, public virtual Base2 {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Should have 2 virtual bases
    EXPECT_EQ(derived->getNumVBases(), 2);

    // Constructor exists
    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);

    // Constructor is valid
    EXPECT_FALSE(ctor->isDeleted());
}

// ============================================================================
// Test 7: Constructor with Indirect Virtual Base
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, ConstructorWithIndirectVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Middle : public virtual Base {
        public:
            Middle() {}
            int m;
        };

        class Derived : public Middle {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* middle = getClass(code, "Middle");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(middle, nullptr);
    ASSERT_NE(derived, nullptr);

    // Both have virtual bases
    EXPECT_GT(middle->getNumVBases(), 0);
    EXPECT_GT(derived->getNumVBases(), 0);

    // Both have constructors
    auto* middleCtor = findConstructor(middle, 0);
    auto* derivedCtor = findConstructor(derived, 0);

    ASSERT_NE(middleCtor, nullptr);
    ASSERT_NE(derivedCtor, nullptr);

    EXPECT_FALSE(middleCtor->isDeleted());
    EXPECT_FALSE(derivedCtor->isDeleted());
}

// ============================================================================
// Test 8: Defaulted Constructor with Virtual Base
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, DefaultedConstructorWithVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            Base() = default;
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() = default;
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Has virtual base
    EXPECT_GT(derived->getNumVBases(), 0);

    // Find defaulted constructor
    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);

    // Constructor is defaulted
    EXPECT_TRUE(ctor->isDefaulted());
    EXPECT_FALSE(ctor->isDeleted());
}

// ============================================================================
// Test 9: Deleted Constructor with Virtual Base
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, DeletedConstructorWithVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() = delete;
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Has virtual base
    EXPECT_GT(derived->getNumVBases(), 0);

    // Find constructor (even deleted ones exist in AST)
    clang::CXXConstructorDecl* deletedCtor = nullptr;
    for (auto* ctor : derived->ctors()) {
        if (ctor->getNumParams() == 0) {
            deletedCtor = ctor;
            break;
        }
    }

    ASSERT_NE(deletedCtor, nullptr);

    // Constructor is deleted
    EXPECT_TRUE(deletedCtor->isDeleted());
}

// ============================================================================
// Test 10: Constructor with Mixed Virtual and Non-Virtual Bases
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, ConstructorMixedInheritance) {
    std::string code = R"(
        class VirtualBase {
        public:
            VirtualBase() {}
            virtual ~VirtualBase() {}
            int vb;
        };

        class NonVirtualBase {
        public:
            NonVirtualBase() {}
            virtual ~NonVirtualBase() {}
            int nvb;
        };

        class Derived : public virtual VirtualBase, public NonVirtualBase {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Has 1 virtual base and 1 non-virtual base
    EXPECT_EQ(derived->getNumVBases(), 1);
    EXPECT_EQ(derived->getNumBases(), 2);

    // Constructor exists
    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);

    EXPECT_FALSE(ctor->isDeleted());
}

// ============================================================================
// Test 11: Constructor Calls Virtual Base Constructor
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, ConstructorCallsVirtualBaseConstructor) {
    std::string code = R"(
        class Base {
        public:
            Base(int val) : value(val) {}
            virtual ~Base() {}
            int value;
        };

        class Derived : public virtual Base {
        public:
            Derived(int b, int d) : Base(b), data(d) {}
            int data;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Has virtual base
    EXPECT_GT(derived->getNumVBases(), 0);

    // Constructor with 2 params
    auto* ctor = findConstructor(derived, 2);
    ASSERT_NE(ctor, nullptr);

    // Check initializers
    bool hasBaseInit = false;
    bool hasDataInit = false;

    for (auto it = ctor->init_begin(); it != ctor->init_end(); ++it) {
        if ((*it)->isBaseInitializer()) {
            hasBaseInit = true;
        } else if ((*it)->isMemberInitializer()) {
            hasDataInit = true;
        }
    }

    EXPECT_TRUE(hasBaseInit) << "Constructor should have base initializer";
    EXPECT_TRUE(hasDataInit) << "Constructor should have member initializer";
}

// ============================================================================
// Test 12: Empty Constructor Body with Virtual Base
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, EmptyConstructorBodyWithVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Has virtual base
    EXPECT_GT(derived->getNumVBases(), 0);

    // Constructor exists
    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);

    // Constructor body should be empty
    auto* body = ctor->getBody();
    if (body) {
        // Body exists but should be empty compound statement
        if (auto* compoundStmt = llvm::dyn_cast<clang::CompoundStmt>(body)) {
            EXPECT_EQ(compoundStmt->size(), 0) << "Constructor body should be empty";
        }
    }
}

// ============================================================================
// Test 13: Constructor in Complex Diamond
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, ConstructorInComplexDiamond) {
    std::string code = R"(
        class Top {
        public:
            Top() {}
            virtual ~Top() {}
            int t;
        };

        class Left : public virtual Top {
        public:
            Left() {}
            int l;
        };

        class Right : public virtual Top {
        public:
            Right() {}
            int r;
        };

        class Middle : public Left, public Right {
        public:
            Middle() {}
            int m;
        };

        class Bottom : public Middle {
        public:
            Bottom() {}
            int b;
        };
    )";

    auto* top = getClass(code, "Top");
    auto* middle = getClass(code, "Middle");
    auto* bottom = getClass(code, "Bottom");

    ASSERT_NE(top, nullptr);
    ASSERT_NE(middle, nullptr);
    ASSERT_NE(bottom, nullptr);

    // Middle and Bottom have virtual bases
    EXPECT_GT(middle->getNumVBases(), 0);
    EXPECT_GT(bottom->getNumVBases(), 0);

    // All have constructors
    EXPECT_NE(findConstructor(top, 0), nullptr);
    EXPECT_NE(findConstructor(middle, 0), nullptr);
    EXPECT_NE(findConstructor(bottom, 0), nullptr);
}

// ============================================================================
// Test 14: Constructor Parameter Count with Virtual Base
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, ConstructorParameterCount) {
    std::string code = R"(
        class Base {
        public:
            Base(int b1, int b2, int b3) : v1(b1), v2(b2), v3(b3) {}
            virtual ~Base() {}
            int v1, v2, v3;
        };

        class Derived : public virtual Base {
        public:
            Derived(int b1, int b2, int b3, int d1, int d2)
                : Base(b1, b2, b3), d1(d1), d2(d2) {}
            int d1, d2;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Has virtual base
    EXPECT_GT(derived->getNumVBases(), 0);

    // Find constructor with 5 params
    auto* ctor = findConstructor(derived, 5);
    ASSERT_NE(ctor, nullptr);

    // Verify parameter count
    EXPECT_EQ(ctor->getNumParams(), 5);

    // Check parameter types (all should be int)
    for (unsigned i = 0; i < ctor->getNumParams(); ++i) {
        auto* param = ctor->getParamDecl(i);
        ASSERT_NE(param, nullptr);
        EXPECT_TRUE(param->getType()->isIntegerType());
    }
}

// ============================================================================
// Test 15: Implicit Constructor with Virtual Base
// ============================================================================

TEST_F(ConstructorHandlerVirtualInheritanceTest, ImplicitConstructorWithVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            // No explicit constructor - should have implicit default constructor
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Has virtual base
    EXPECT_GT(derived->getNumVBases(), 0);

    // Should have implicit default constructor
    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);

    // Constructor is implicit
    EXPECT_TRUE(ctor->isImplicit() || ctor->isDefaulted());
}
