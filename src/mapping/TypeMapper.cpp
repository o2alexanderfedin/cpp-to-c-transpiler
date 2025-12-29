/**
 * @file TypeMapper.cpp
 * @brief Implementation of TypeMapper for C++ → C type mappings
 */

#include "mapping/TypeMapper.h"
#include "llvm/Support/raw_ostream.h"

namespace cpptoc {

void TypeMapper::setCreatedType(const clang::Type* cppType, clang::QualType cType) {
    if (!cppType || cType.isNull()) {
        llvm::outs() << "[TypeMapper::setCreatedType] Warning: null argument\n";
        return;
    }

    cppToCTypeMap_[cppType] = cType;

    llvm::outs() << "[TypeMapper::setCreatedType] Mapped C++ type " << (const void*)cppType
                 << " (" << clang::QualType(cppType, 0).getAsString() << ")"
                 << " → C type " << cType.getAsString() << "\n";
}

clang::QualType TypeMapper::getCreatedType(const clang::Type* cppType) const {
    if (!cppType) {
        llvm::outs() << "[TypeMapper::getCreatedType] Warning: nullptr cppType\n";
        return clang::QualType();
    }

    auto it = cppToCTypeMap_.find(cppType);
    if (it != cppToCTypeMap_.end()) {
        llvm::outs() << "[TypeMapper::getCreatedType] Found C type " << it->second.getAsString()
                     << " for C++ type " << (const void*)cppType << "\n";
        return it->second;
    }

    llvm::outs() << "[TypeMapper::getCreatedType] Warning: No C type found for C++ type "
                 << (const void*)cppType << " (" << clang::QualType(cppType, 0).getAsString() << ")\n";
    return clang::QualType();
}

bool TypeMapper::hasCreatedType(const clang::Type* cppType) const {
    if (!cppType) {
        return false;
    }
    return cppToCTypeMap_.find(cppType) != cppToCTypeMap_.end();
}

} // namespace cpptoc
