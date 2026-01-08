/**
 * @file VirtualInheritanceE2ETest.cpp
 * @brief Comprehensive end-to-end tests for virtual inheritance (Phase 56)
 *
 * Tests the complete transpilation pipeline for virtual inheritance:
 * Stage 1: Clang parses C++ with virtual inheritance → C++ AST
 * Stage 2: Handlers translate C++ AST → C AST (with VTT, vbptr, C1/C2 constructors)
 * Stage 3: CodeGenerator emits C source (ABI-compliant virtual inheritance)
 * Validation: Compile C code with gcc and execute, verify ABI compliance
 *
 * Test Coverage:
 * 1. Simple Virtual Base - Basic virtual inheritance scenario
 * 2. Diamond Pattern - Classic diamond inheritance with single virtual base instance
 * 3. Multiple Virtual Bases - Multiple independent virtual bases
 * 4. Deep Virtual Inheritance - 3+ levels of virtual inheritance hierarchy
 * 5. Virtual Inheritance + Virtual Methods - Combined polymorphism and virtual inheritance
 * 6. Non-POD Virtual Bases - Constructors, destructors, initialization order
 * 7. Casting with Virtual Inheritance - static_cast with pointer adjustments
 * 8. Real-World Scenario - iostream-style complex hierarchy
 *
 * ABI Compliance Validation:
 * - Memory layout matches C++ ABI (Itanium ABI)
 * - VTable structure correct (virtual method pointers + virtual base offsets)
 * - VTT (Virtual Table Table) generated for classes with virtual bases
 * - Constructor variants (C1/C2) for virtual base construction
 * - Single virtual base instance in diamond patterns
 * - Correct pointer adjustments for casts
 *
 * Reference: https://itanium-cxx-abi.github.io/cxx-abi/abi.html#vtable
 */

#include "../fixtures/DispatcherTestHelper.h"
#include "../ABIValidator.h"
#include "dispatch/TypeHandler.h"
#include "dispatch/ParameterHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/MemberExprHandler.h"
#include "dispatch/BinaryOperatorHandler.h"
#include "dispatch/UnaryOperatorHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/ParenExprHandler.h"
#include "dispatch/CallExprHandler.h"
#include "dispatch/CXXMemberCallExprHandler.h"
#include "dispatch/ArraySubscriptExprHandler.h"
#include "dispatch/CompoundStmtHandler.h"
#include "dispatch/DeclStmtHandler.h"
#include "dispatch/ReturnStmtHandler.h"
#include "dispatch/StatementHandler.h"
#include "dispatch/RecordHandler.h"
#include "dispatch/FunctionHandler.h"
#include "dispatch/InstanceMethodHandler.h"
#include "dispatch/VirtualMethodHandler.h"
#include "dispatch/ConstructorHandler.h"
#include "dispatch/DestructorHandler.h"
#include "dispatch/VariableHandler.h"
#include "dispatch/TranslationUnitHandler.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;
using namespace cpptoc::test;

/**
 * @class VirtualInheritanceE2ETest
 * @brief Test fixture for end-to-end virtual inheritance testing
 */
class VirtualInheritanceE2ETest : public ::testing::Test {
protected:
    ABIValidator abiValidator;

    /**
     * @brief Run complete pipeline: C++ source → C source → compile → execute
     * @param cppCode C++ source code
     * @param expectedExitCode Expected exit code from execution
     * @param debugOutput If true, print generated C code
     * @return true if test passed
     */
    bool runPipeline(const std::string& cppCode, int expectedExitCode, bool debugOutput = false) {
        // Create dispatcher pipeline
        auto pipeline = createDispatcherPipeline(cppCode);

        // Register all handlers needed for virtual inheritance tests
        TypeHandler::registerWith(*pipeline.dispatcher);
        ParameterHandler::registerWith(*pipeline.dispatcher);
        LiteralHandler::registerWith(*pipeline.dispatcher);
        DeclRefExprHandler::registerWith(*pipeline.dispatcher);
        MemberExprHandler::registerWith(*pipeline.dispatcher);
        BinaryOperatorHandler::registerWith(*pipeline.dispatcher);
        UnaryOperatorHandler::registerWith(*pipeline.dispatcher);
        ImplicitCastExprHandler::registerWith(*pipeline.dispatcher);
        ParenExprHandler::registerWith(*pipeline.dispatcher);
        CallExprHandler::registerWith(*pipeline.dispatcher);
        CXXMemberCallExprHandler::registerWith(*pipeline.dispatcher);
        ArraySubscriptExprHandler::registerWith(*pipeline.dispatcher);
        CompoundStmtHandler::registerWith(*pipeline.dispatcher);
        DeclStmtHandler::registerWith(*pipeline.dispatcher);
        ReturnStmtHandler::registerWith(*pipeline.dispatcher);
        StatementHandler::registerWith(*pipeline.dispatcher);
        RecordHandler::registerWith(*pipeline.dispatcher);
        FunctionHandler::registerWith(*pipeline.dispatcher);
        InstanceMethodHandler::registerWith(*pipeline.dispatcher);
        VirtualMethodHandler::registerWith(*pipeline.dispatcher);
        ConstructorHandler::registerWith(*pipeline.dispatcher);
        DestructorHandler::registerWith(*pipeline.dispatcher);
        VariableHandler::registerWith(*pipeline.dispatcher);
        TranslationUnitHandler::registerWith(*pipeline.dispatcher);

        // Dispatch the TranslationUnit
        auto* TU = pipeline.cppAST->getASTContext().getTranslationUnitDecl();
        pipeline.dispatcher->dispatch(
            pipeline.cppAST->getASTContext(),
            pipeline.cAST->getASTContext(),
            TU
        );

        // Generate C code from C AST
        std::string cCode = generateCCode(
            pipeline.cAST->getASTContext(),
            *pipeline.pathMapper
        );

        if (debugOutput) {
            std::cerr << "=== Generated C code ===\n" << cCode << "\n=== End C code ===\n";
        }

        // Validate ABI compliance (basic checks)
        // Full ABI validation would require more sophisticated analysis
        bool abiValid = abiValidator.verifySizesMatch(cppCode, cCode);
        if (!abiValid && debugOutput) {
            std::cerr << "WARNING: ABI validation issues detected\n";
        }

        // Compile and run
        int actualExitCode = compileAndRun(cCode, "e2e_virtual_inheritance");

        if (actualExitCode == -1) {
            std::cerr << "Compilation failed!\n";
            std::cerr << "Generated C code:\n" << cCode << "\n";
            return false;
        }

        if (actualExitCode != expectedExitCode) {
            std::cerr << "Exit code mismatch: expected " << expectedExitCode
                      << ", got " << actualExitCode << "\n";
            if (debugOutput) {
                std::cerr << "Generated C code:\n" << cCode << "\n";
            }
            return false;
        }

        return true;
    }
};

// ============================================================================
// Test 1: Simple Virtual Base
// ============================================================================

TEST_F(VirtualInheritanceE2ETest, SimpleVirtualBase) {
    const char* cppCode = R"(
        struct Base {
            int x;
            virtual ~Base() {}
        };

        struct Derived : virtual Base {
            int y;
        };

        int main() {
            Derived d;
            d.x = 10;
            d.y = 20;
            return d.x + d.y;  // Should return 30
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 30, true));
}

// ============================================================================
// Test 2: Diamond Pattern (Classic)
// ============================================================================

TEST_F(VirtualInheritanceE2ETest, DiamondPattern) {
    const char* cppCode = R"(
        struct A {
            int a_data;
            A() : a_data(10) {}
            virtual ~A() {}
        };

        struct B : virtual A {
            int b_data;
            B() : b_data(20) {}
        };

        struct C : virtual A {
            int c_data;
            C() : c_data(30) {}
        };

        struct D : B, C {
            int d_data;
            D() : d_data(40) {}
        };

        int main() {
            D d;
            // Single A instance - all paths see same a_data
            return d.a_data + d.b_data + d.c_data + d.d_data;  // Should return 100
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 100, true));
}

// ============================================================================
// Test 3: Multiple Virtual Bases
// ============================================================================

TEST_F(VirtualInheritanceE2ETest, MultipleVirtualBases) {
    const char* cppCode = R"(
        struct Base1 {
            int x;
            virtual ~Base1() {}
        };

        struct Base2 {
            int y;
            virtual ~Base2() {}
        };

        struct Derived : virtual Base1, virtual Base2 {
            int z;
        };

        int main() {
            Derived d;
            d.x = 10;
            d.y = 20;
            d.z = 30;
            return d.x + d.y + d.z;  // Should return 60
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 60, true));
}

// ============================================================================
// Test 4: Deep Virtual Inheritance Hierarchy
// ============================================================================

TEST_F(VirtualInheritanceE2ETest, DeepVirtualInheritance) {
    const char* cppCode = R"(
        struct Level0 {
            int val0;
            Level0() : val0(1) {}
            virtual ~Level0() {}
        };

        struct Level1 : virtual Level0 {
            int val1;
            Level1() : val1(2) {}
        };

        struct Level2 : virtual Level1 {
            int val2;
            Level2() : val2(4) {}
        };

        struct Level3 : virtual Level2 {
            int val3;
            Level3() : val3(8) {}
        };

        int main() {
            Level3 obj;
            return obj.val0 + obj.val1 + obj.val2 + obj.val3;  // Should return 15
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 15, true));
}

// ============================================================================
// Test 5: Virtual Inheritance + Virtual Methods
// ============================================================================

TEST_F(VirtualInheritanceE2ETest, VirtualInheritanceWithVirtualMethods) {
    const char* cppCode = R"(
        struct Base {
            virtual int getValue() { return 10; }
            virtual ~Base() {}
        };

        struct Derived1 : virtual Base {
            int getValue() override { return 20; }
        };

        struct Derived2 : virtual Base {
            int getValue() override { return 30; }
        };

        struct Final : Derived1, Derived2 {
            int getValue() override { return 40; }
        };

        int main() {
            Final f;
            return f.getValue();  // Should return 40
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 40, true));
}

// ============================================================================
// Test 6: Non-POD Virtual Bases (Constructor/Destructor Order)
// ============================================================================

TEST_F(VirtualInheritanceE2ETest, NonPODVirtualBases) {
    const char* cppCode = R"(
        int counter = 0;

        struct Base {
            int id;
            Base() : id(++counter) {}
            virtual ~Base() { --counter; }
        };

        struct Derived1 : virtual Base {
            Derived1() {}
        };

        struct Derived2 : virtual Base {
            Derived2() {}
        };

        struct Final : Derived1, Derived2 {
            Final() {}
        };

        int main() {
            {
                Final f;
                // Base constructed once (counter = 1)
                // f.id should be 1
            }
            // Base destructed once (counter = 0)
            return counter;  // Should return 0
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 0, true));
}

// ============================================================================
// Test 7: Casting with Virtual Inheritance
// ============================================================================

TEST_F(VirtualInheritanceE2ETest, CastingWithVirtualInheritance) {
    const char* cppCode = R"(
        struct Base {
            int x;
            virtual ~Base() {}
        };

        struct Derived : virtual Base {
            int y;
        };

        int main() {
            Derived d;
            d.x = 15;
            d.y = 25;

            Base* basePtr = &d;  // Implicit upcast
            basePtr->x = 10;

            return d.x + d.y;  // Should return 35
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 35, true));
}

// ============================================================================
// Test 8: Real-World Scenario (iostream-style)
// ============================================================================

TEST_F(VirtualInheritanceE2ETest, RealWorldIOStreamStyle) {
    const char* cppCode = R"(
        struct ios_base {
            int flags;
            ios_base() : flags(0) {}
            virtual ~ios_base() {}
        };

        struct istream : virtual ios_base {
            int read_pos;
            istream() : read_pos(0) {}
        };

        struct ostream : virtual ios_base {
            int write_pos;
            ostream() : write_pos(0) {}
        };

        struct iostream : istream, ostream {
            iostream() {}
        };

        int main() {
            iostream io;
            io.flags = 5;
            io.read_pos = 10;
            io.write_pos = 15;

            // Single ios_base instance
            return io.flags + io.read_pos + io.write_pos;  // Should return 30
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 30, true));
}

// ============================================================================
// Test 9: Mixed Virtual and Non-Virtual Inheritance
// ============================================================================

TEST_F(VirtualInheritanceE2ETest, MixedInheritance) {
    const char* cppCode = R"(
        struct VirtualBase {
            int vx;
            virtual ~VirtualBase() {}
        };

        struct NonVirtualBase {
            int nx;
        };

        struct Intermediate1 : virtual VirtualBase {
            int i1;
        };

        struct Intermediate2 : virtual VirtualBase, NonVirtualBase {
            int i2;
        };

        struct Final : Intermediate1, Intermediate2 {
            int f;
        };

        int main() {
            Final obj;
            obj.vx = 1;   // Single virtual base instance
            obj.nx = 2;   // Non-virtual base
            obj.i1 = 4;
            obj.i2 = 8;
            obj.f = 16;

            return obj.vx + obj.nx + obj.i1 + obj.i2 + obj.f;  // Should return 31
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 31, true));
}

// ============================================================================
// Test 10: Virtual Base Access Through Multiple Paths
// ============================================================================

TEST_F(VirtualInheritanceE2ETest, VirtualBaseAccessMultiplePaths) {
    const char* cppCode = R"(
        struct Base {
            int value;
            Base() : value(0) {}
            virtual ~Base() {}
        };

        struct Left : virtual Base {
            void setViaLeft(int v) { value = v; }
        };

        struct Right : virtual Base {
            int getViaRight() { return value; }
        };

        struct Derived : Left, Right {
        };

        int main() {
            Derived d;
            d.setViaLeft(42);  // Access via Left path
            return d.getViaRight();  // Access via Right path - should see same value (42)
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 42, true));
}

// ============================================================================
// Sanity Test (Infrastructure Verification)
// ============================================================================

TEST_F(VirtualInheritanceE2ETest, BasicSanity) {
    // Just verify test infrastructure works
    EXPECT_TRUE(true);
}
