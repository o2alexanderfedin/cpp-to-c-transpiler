/**
 * @file HandlerTestFixture.h
 * @brief Base test fixture for handler unit tests
 *
 * Provides common setup/teardown and helper methods for all handler tests.
 * Reduces boilerplate and ensures consistent test structure.
 *
 * Design Principles:
 * - DRY: Common test setup logic in one place
 * - Single Responsibility: Only test fixture setup
 * - Template Method: Subclasses can override SetUp/TearDown
 */

#pragma once

#include "MockASTContext.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include <gtest/gtest.h>
#include <memory>

namespace cpptoc {
namespace test {

/**
 * @class HandlerTestFixture
 * @brief Base class for all handler unit tests
 *
 * Provides:
 * - MockASTContext for creating C++ AST nodes
 * - CNodeBuilder for creating C AST nodes
 * - HandlerContext for handler translation
 * - Helper assertion methods
 *
 * Usage:
 * @code
 *   class FunctionHandlerTest : public HandlerTestFixture {};
 *
 *   TEST_F(FunctionHandlerTest, SimpleFunction) {
 *       auto* cppFunc = getMock().createFunction("int", "foo", {});
 *       // ... test logic ...
 *   }
 * @endcode
 */
class HandlerTestFixture : public ::testing::Test {
protected:
    /// Mock AST context for C++ nodes
    std::unique_ptr<MockASTContext> mockCpp_;

    /// Mock AST context for C nodes
    std::unique_ptr<MockASTContext> mockC_;

    /// C node builder
    std::unique_ptr<clang::CNodeBuilder> builder_;

    /// Handler context
    std::unique_ptr<HandlerContext> context_;

    /**
     * @brief Setup test fixture
     *
     * Called before each test. Creates mock contexts, builder, and handler context.
     */
    void SetUp() override;

    /**
     * @brief Teardown test fixture
     *
     * Called after each test. Cleans up resources in reverse order.
     */
    void TearDown() override;

    // ========================================================================
    // Accessor Methods
    // ========================================================================

    /**
     * @brief Get C++ mock AST context
     * @return Reference to MockASTContext for C++
     */
    MockASTContext& getMockCpp() { return *mockCpp_; }

    /**
     * @brief Get C mock AST context
     * @return Reference to MockASTContext for C
     */
    MockASTContext& getMockC() { return *mockC_; }

    /**
     * @brief Get handler context
     * @return Reference to HandlerContext
     */
    HandlerContext& getContext() { return *context_; }

    /**
     * @brief Get C node builder
     * @return Reference to CNodeBuilder
     */
    clang::CNodeBuilder& getBuilder() { return *builder_; }

    // ========================================================================
    // Helper Assertion Methods
    // ========================================================================

    /**
     * @brief Assert function declaration matches expected properties
     * @param actual Function declaration to check
     * @param expectedName Expected function name
     * @param expectedReturnType Expected return type string
     * @param expectedParamCount Expected parameter count
     */
    void assertFunctionEquals(
        clang::FunctionDecl* actual,
        const std::string& expectedName,
        const std::string& expectedReturnType,
        size_t expectedParamCount
    );

    /**
     * @brief Assert that translation produced non-null result
     * @param result Translation result
     * @param message Optional failure message
     */
    void assertTranslated(clang::Decl* result, const char* message = "Translation failed");

    /**
     * @brief Assert that C AST node has expected type
     * @tparam T Expected node type
     * @param node Node to check
     * @return Casted node pointer
     */
    template<typename T>
    T* assertNodeType(clang::Decl* node) {
        auto* typed = llvm::dyn_cast_or_null<T>(node);
        EXPECT_NE(typed, nullptr) << "Node is not of expected type";
        return typed;
    }
};

} // namespace test
} // namespace cpptoc
