/**
 * @file E2ETestExample_DISPATCHER_PATTERN.cpp
 * @brief EXAMPLE: How to write E2E tests using the new dispatcher pattern
 *
 * This file demonstrates the correct pattern for E2E tests after
 * HandlerContext retirement. Use this as a template for migrating
 * the 7 disabled E2E test files.
 *
 * Disabled E2E tests that need migration:
 * - tests/e2e/phase1/E2EPhase1Test.cpp
 * - tests/e2e/phase2/ControlFlowE2ETest.cpp
 * - tests/e2e/phase3/GlobalVariablesE2ETest.cpp
 * - tests/e2e/phase4/PointersE2ETest.cpp
 * - tests/e2e/phase5/StructsE2ETest.cpp
 * - tests/e2e/phase6/ClassesE2ETest.cpp
 * - tests/e2e/phase46/MultipleInheritanceE2ETest.cpp
 */

#include "tests/fixtures/DispatcherTestHelper.h"
#include "dispatch/FunctionHandler.h"
#include "dispatch/VariableHandler.h"
#include "dispatch/RecordHandler.h"
#include <gtest/gtest.h>

using namespace cpptoc;

/**
 * @class E2EExampleTest
 * @brief Example test fixture for dispatcher-based E2E testing
 */
class E2EExampleTest : public ::testing::Test {
protected:
    /**
     * @brief Run complete pipeline with dispatcher pattern
     * @param cppCode C++ source code
     * @param expectedExitCode Expected exit code from execution
     * @return true if test passed
     */
    bool runPipeline(const std::string& cppCode, int expectedExitCode) {
        // Create dispatcher pipeline
        auto pipeline = cpptoc::test::createDispatcherPipeline(cppCode);

        // Register handlers needed for this test
        // Note: Register in dependency order - types before functions, etc.
        FunctionHandler::registerWith(*pipeline.dispatcher);
        VariableHandler::registerWith(*pipeline.dispatcher);
        RecordHandler::registerWith(*pipeline.dispatcher);

        // Dispatch all top-level declarations from C++ AST
        for (auto* decl : pipeline.cppAST->getASTContext().getTranslationUnitDecl()->decls()) {
            // Cast away const for dispatch
            auto* nonConstDecl = const_cast<clang::Decl*>(decl);

            // Dispatch to appropriate handler
            bool handled = pipeline.dispatcher->dispatch(
                pipeline.cppAST->getASTContext(),
                pipeline.cAST->getASTContext(),
                nonConstDecl
            );

            if (!handled) {
                std::cerr << "Warning: No handler for declaration\n";
            }
        }

        // Generate C code from C AST
        std::string cCode = cpptoc::test::generateCCode(pipeline.cAST->getASTContext());

        // Compile and run
        int actualExitCode = cpptoc::test::compileAndRun(cCode, "e2e_example");

        if (actualExitCode == -1) {
            std::cerr << "Compilation failed!\n";
            std::cerr << "Generated C code:\n" << cCode << "\n";
            return false;
        }

        return actualExitCode == expectedExitCode;
    }
};

// ============================================================================
// Example Test: Simple Addition
// ============================================================================

TEST_F(E2EExampleTest, SimpleAddition) {
    std::string cppCode = R"(
        int add(int a, int b) {
            return a + b;
        }
        int main() {
            return add(3, 4);
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 7)) << "Expected exit code 7 (3+4)";
}

// ============================================================================
// Example Test: Local Variables
// ============================================================================

TEST_F(E2EExampleTest, LocalVariables) {
    std::string cppCode = R"(
        int main() {
            int x = 5;
            int y = 3;
            return x + y;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 8)) << "Expected exit code 8 (5+3)";
}

// ============================================================================
// Example Test: Simple Struct
// ============================================================================

TEST_F(E2EExampleTest, SimpleStruct) {
    std::string cppCode = R"(
        struct Point {
            int x;
            int y;
        };

        int main() {
            Point p;
            p.x = 5;
            p.y = 3;
            return p.x + p.y;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 8)) << "Expected exit code 8 (5+3)";
}

/**
 * MIGRATION CHECKLIST FOR DISABLED E2E TESTS:
 *
 * 1. Remove old includes:
 *    - Remove: #include "handlers/HandlerContext.h"
 *    - Remove: #include "CNodeBuilder.h" (if not used directly)
 *
 * 2. Add new includes:
 *    + Add: #include "tests/fixtures/DispatcherTestHelper.h"
 *    + Add: #include "dispatch/XxxHandler.h" (for each handler you need)
 *
 * 3. Remove old test fixture setup:
 *    - Remove: std::unique_ptr<XxxHandler> members
 *    - Remove: SetUp() method that instantiates handlers
 *
 * 4. Update runPipeline() method:
 *    - Replace HandlerContext instantiation with pipeline creation
 *    - Replace handler->handleDecl() calls with dispatcher->dispatch()
 *    - Use the pattern from this example file
 *
 * 5. Register only needed handlers:
 *    - Don't register all handlers - only what each test needs
 *    - Register in dependency order (types before functions, etc.)
 *
 * 6. Build and test:
 *    - Uncomment test target in CMakeLists.txt
 *    - Build: cmake --build build --target YourTestName
 *    - Run: build/YourTestName
 *    - Fix any compilation errors
 *    - Fix any runtime failures
 *
 * 7. Common issues:
 *    - Handler not registered → dispatch returns false
 *    - Wrong handler order → missing dependencies
 *    - AST context mismatch → const_cast needed for dispatch
 */
