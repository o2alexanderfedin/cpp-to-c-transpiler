/**
 * @file DeclMapper.cpp
 * @brief Implementation of DeclMapper for C++ → C declaration mappings
 */

#include "mapping/DeclMapper.h"
#include "llvm/Support/raw_ostream.h"

namespace cpptoc {

void DeclMapper::setCreatedDecl(const clang::Decl* cppDecl, clang::Decl* cDecl) {
    if (!cppDecl || !cDecl) {
        llvm::outs() << "[DeclMapper::setCreatedDecl] Warning: nullptr argument\n";
        return;
    }

    cppToCDeclMap_[cppDecl] = cDecl;

    llvm::outs() << "[DeclMapper::setCreatedDecl] Mapped C++ decl " << (const void*)cppDecl
                 << " → C decl " << (const void*)cDecl << "\n";
}

clang::Decl* DeclMapper::getCreatedDecl(const clang::Decl* cppDecl) const {
    if (!cppDecl) {
        llvm::outs() << "[DeclMapper::getCreatedDecl] Warning: nullptr cppDecl\n";
        return nullptr;
    }

    auto it = cppToCDeclMap_.find(cppDecl);
    if (it != cppToCDeclMap_.end()) {
        llvm::outs() << "[DeclMapper::getCreatedDecl] Found C decl " << (const void*)it->second
                     << " for C++ decl " << (const void*)cppDecl << "\n";
        return it->second;
    }

    llvm::outs() << "[DeclMapper::getCreatedDecl] Warning: No C decl found for C++ decl "
                 << (const void*)cppDecl << "\n";
    return nullptr;
}

} // namespace cpptoc
