/**
 * @file ExprMapper.cpp
 * @brief Implementation of ExprMapper
 */

#include "mapping/ExprMapper.h"

namespace cpptoc {

void ExprMapper::setCreatedExpr(const clang::Expr* cppExpr, clang::Expr* cExpr) {
    cppToCExprMap_[cppExpr] = cExpr;
}

clang::Expr* ExprMapper::getCreatedExpr(const clang::Expr* cppExpr) const {
    auto it = cppToCExprMap_.find(cppExpr);
    if (it != cppToCExprMap_.end()) {
        return it->second;
    }
    return nullptr;
}

bool ExprMapper::hasCreatedExpr(const clang::Expr* cppExpr) const {
    return cppToCExprMap_.find(cppExpr) != cppToCExprMap_.end();
}

} // namespace cpptoc
