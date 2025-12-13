/**
 * @file VirtualCallTranslator.cpp
 * @brief Implementation of Story #172: Virtual Call Translation
 */

#include "VirtualCallTranslator.h"
#include "clang/AST/DeclCXX.h"

using namespace clang;

VirtualCallTranslator::VirtualCallTranslator(ASTContext& Context, VirtualMethodAnalyzer& Analyzer)
    : Context(Context), Analyzer(Analyzer) {}

bool VirtualCallTranslator::isVirtualCall(const CXXMemberCallExpr* CallExpr) const {
    if (!CallExpr) {
        return false;
    }

    // Get the method being called
    const CXXMethodDecl* Method = dyn_cast_or_null<CXXMethodDecl>(CallExpr->getMethodDecl());
    if (!Method) {
        return false;
    }

    // Check if method is virtual
    return Method->isVirtual();
}

std::string VirtualCallTranslator::getVtableMethodName(const CXXMethodDecl* Method) const {
    if (!Method) {
        return "";
    }

    // Special case: destructor
    if (isa<CXXDestructorDecl>(Method)) {
        return "destructor";
    }

    // Regular method: use method name
    return Method->getNameAsString();
}
