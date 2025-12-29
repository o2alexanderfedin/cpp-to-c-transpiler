/**
 * @file ExprMapper.h
 * @brief Maps C++ source expressions to created C target expressions
 *
 * Single Responsibility: Manage C++ → C expression mappings for the transpiler.
 *
 * This class enables the Chain of Responsibility pattern by allowing:
 * - ExpressionHandler to store created C expressions
 * - Other handlers to retrieve C expressions created by ExpressionHandler
 *
 * Example:
 * - BinaryOperatorHandler creates C BinaryOperator and stores: exprMapper.setCreatedExpr(cppBinOp, cBinOp)
 * - ReturnStmtHandler retrieves: cBinOp = exprMapper.getCreatedExpr(cppBinOp)
 *
 * Design Principles:
 * - Single Responsibility: Only manages expression mappings
 * - Separation from DeclMapper: DeclMapper maps declarations, ExprMapper maps expressions
 * - Separation from TypeMapper: TypeMapper maps types, ExprMapper maps expressions
 */

#pragma once

#include "clang/AST/Expr.h"
#include <map>

namespace cpptoc {

/**
 * @class ExprMapper
 * @brief Manages mappings from C++ expressions to created C expressions
 *
 * Responsibilities:
 * - Store C++ → C expression mappings
 * - Retrieve C expressions for given C++ expressions
 * - Support Chain of Responsibility pattern for handlers
 */
class ExprMapper {
public:
    /**
     * @brief Default constructor
     */
    ExprMapper() = default;

    /**
     * @brief Store mapping from C++ expression to created C expression
     * @param cppExpr Source C++ expression
     * @param cExpr Created C expression
     *
     * Enables handlers to retrieve expressions created by expression handlers.
     *
     * Example:
     * ```cpp
     * // BinaryOperatorHandler creates C binary operator and stores mapping
     * clang::BinaryOperator* cBinOp = createBinaryOperator(...);
     * exprMapper.setCreatedExpr(cppBinOp, cBinOp);
     *
     * // ReturnStmtHandler retrieves created expression
     * clang::Expr* cExpr = exprMapper.getCreatedExpr(cppBinOp);
     * ```
     */
    void setCreatedExpr(const clang::Expr* cppExpr, clang::Expr* cExpr);

    /**
     * @brief Get C expression created for a C++ expression
     * @param cppExpr Source C++ expression
     * @return Created C expression, or nullptr if not found
     *
     * Retrieves C expression previously stored via setCreatedExpr().
     * Returns nullptr if no mapping exists for the given C++ expression.
     */
    clang::Expr* getCreatedExpr(const clang::Expr* cppExpr) const;

    /**
     * @brief Check if a C++ expression has a mapped C expression
     * @param cppExpr Source C++ expression
     * @return true if mapping exists, false otherwise
     */
    bool hasCreatedExpr(const clang::Expr* cppExpr) const;

private:
    std::map<const clang::Expr*, clang::Expr*> cppToCExprMap_;
    ///< Maps C++ source expressions to created C expressions
    ///< Example: C++ BinaryOperator → C BinaryOperator, C++ IntegerLiteral → C IntegerLiteral
};

} // namespace cpptoc
