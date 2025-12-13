/**
 * @file PureVirtualHandler.cpp
 * @brief Implementation of Story #173: Pure Virtual Function Support
 */

#include "PureVirtualHandler.h"
#include "clang/AST/DeclCXX.h"

using namespace clang;

PureVirtualHandler::PureVirtualHandler(ASTContext& Context, VirtualMethodAnalyzer& Analyzer)
    : Context(Context), Analyzer(Analyzer) {}

bool PureVirtualHandler::isPureVirtual(const CXXMethodDecl* Method) const {
    if (!Method) {
        return false;
    }

    // Delegate to analyzer
    return Analyzer.isPureVirtual(Method);
}

bool PureVirtualHandler::isAbstractClass(const CXXRecordDecl* Record) const {
    if (!Record || !Record->isCompleteDefinition()) {
        return false;
    }

    // Delegate to analyzer
    return Analyzer.isAbstractClass(Record);
}

std::vector<CXXMethodDecl*> PureVirtualHandler::getPureVirtualMethods(
    const CXXRecordDecl* Record) const {

    std::vector<CXXMethodDecl*> pureVirtualMethods;

    if (!Record || !Record->isCompleteDefinition()) {
        return pureVirtualMethods;
    }

    // Iterate through all methods in this class
    for (auto* method : Record->methods()) {
        if (isPureVirtual(method)) {
            pureVirtualMethods.push_back(method);
        }
    }

    return pureVirtualMethods;
}
