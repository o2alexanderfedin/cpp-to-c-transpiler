/**
 * @file StmtMapper.cpp
 * @brief Implementation of StmtMapper for C++ → C statement mappings
 */

#include "mapping/StmtMapper.h"
#include <cassert>

namespace cpptoc {

void StmtMapper::setCreatedStmt(const clang::Stmt* cppStmt, clang::Stmt* cStmt) {
    assert(cppStmt && "C++ statement must not be null");
    assert(cStmt && "C statement must not be null");

    cppToCStmtMap_[cppStmt] = cStmt;
}

clang::Stmt* StmtMapper::getCreatedStmt(const clang::Stmt* cppStmt) const {
    assert(cppStmt && "C++ statement must not be null");

    auto it = cppToCStmtMap_.find(cppStmt);
    return (it != cppToCStmtMap_.end()) ? it->second : nullptr;
}

bool StmtMapper::hasCreatedStmt(const clang::Stmt* cppStmt) const {
    assert(cppStmt && "C++ statement must not be null");

    return cppToCStmtMap_.find(cppStmt) != cppToCStmtMap_.end();
}

} // namespace cpptoc
