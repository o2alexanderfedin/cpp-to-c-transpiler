/**
 * @file TestASTHelper.h
 * @brief Simplified test helper that wraps CNodeBuilder
 *
 * This is a pragmatic approach: instead of creating a full MockASTContext,
 * we leverage the existing CNodeBuilder which already handles AST creation.
 * For testing handlers, we just need to create C++ and C AST nodes.
 */

#pragma once

#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include <memory>
#include <string>

namespace cpptoc {
namespace test {

/**
 * @class TestASTHelper
 * @brief Helper for creating AST contexts for testing
 *
 * Creates real Clang ASTContexts using clang::tooling::buildASTFromCode.
 * This gives us fully functional contexts without complex setup.
 */
class TestASTHelper {
private:
    std::unique_ptr<clang::ASTUnit> cppAST_;
    std::unique_ptr<clang::ASTUnit> cAST_;

public:
    /**
     * @brief Construct test helper with minimal code
     */
    TestASTHelper();

    /**
     * @brief Get C++ AST context
     */
    clang::ASTContext& getCppContext();

    /**
     * @brief Get C AST context
     */
    clang::ASTContext& getCContext();
};

} // namespace test
} // namespace cpptoc
