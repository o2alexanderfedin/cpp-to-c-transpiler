/**
 * @file VirtualMethodAnalyzer.cpp
 * @brief Implementation of VirtualMethodAnalyzer
 */

#include "../include/VirtualMethodAnalyzer.h"
#include "llvm/Config/llvm-config.h"  // For LLVM_VERSION_MAJOR
#include "clang/AST/DeclCXX.h"

using namespace clang;

VirtualMethodAnalyzer::VirtualMethodAnalyzer(ASTContext& Context)
    : Context(Context) {}

bool VirtualMethodAnalyzer::isPolymorphic(const CXXRecordDecl* Record) const {
    if (!Record) {
        return false;
    }

    // Clang's built-in polymorphic check
    return Record->isPolymorphic();
}

std::vector<CXXMethodDecl*> VirtualMethodAnalyzer::getVirtualMethods(
    const CXXRecordDecl* Record) const {
    std::vector<CXXMethodDecl*> virtualMethods;

    if (!Record) {
        return virtualMethods;
    }

    // Iterate through all methods in the class
    for (auto* Method : Record->methods()) {
        // Check if method is virtual (including override)
        if (Method->isVirtual()) {
            virtualMethods.push_back(Method);
        }
    }

    return virtualMethods;
}

bool VirtualMethodAnalyzer::isPureVirtual(const CXXMethodDecl* Method) const {
    if (!Method) {
        return false;
    }

    // Check if method is pure virtual (= 0)
#if LLVM_VERSION_MAJOR >= 16
    return Method->isPureVirtual();
#else
    // LLVM 15 uses isPure() instead of isPureVirtual()
    return Method->isPure();
#endif
}

bool VirtualMethodAnalyzer::isAbstractClass(const CXXRecordDecl* Record) const {
    if (!Record) {
        return false;
    }

    // Clang's built-in abstract class check
    // A class is abstract if it has at least one pure virtual method
    return Record->isAbstract();
}
