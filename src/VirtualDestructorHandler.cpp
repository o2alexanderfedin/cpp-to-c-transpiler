/**
 * @file VirtualDestructorHandler.cpp
 * @brief Implementation of Story #174: Virtual Destructor Handling
 */

#include "VirtualDestructorHandler.h"
#include "clang/AST/DeclCXX.h"

using namespace clang;

VirtualDestructorHandler::VirtualDestructorHandler(ASTContext& Context,
                                                    VirtualMethodAnalyzer& Analyzer)
    : Context(Context), Analyzer(Analyzer) {}

bool VirtualDestructorHandler::isVirtualDestructor(const CXXDestructorDecl* Destructor) const {
    if (!Destructor) {
        return false;
    }

    // Check if destructor is virtual (explicitly or through inheritance)
    return Destructor->isVirtual();
}

bool VirtualDestructorHandler::hasVirtualDestructor(const CXXRecordDecl* Record) const {
    if (!Record || !Record->isCompleteDefinition()) {
        return false;
    }

    // Get the destructor (explicit or implicit)
    CXXDestructorDecl* Destructor = Record->getDestructor();
    if (!Destructor) {
        return false;
    }

    // Check if it's virtual
    return isVirtualDestructor(Destructor);
}

std::string VirtualDestructorHandler::getDestructorVtableName(
    const CXXDestructorDecl* Destructor) const {

    if (!Destructor) {
        return "";
    }

    // Standard vtable name for destructors
    return "destructor";
}

bool VirtualDestructorHandler::shouldDestructorBeFirstInVtable(
    const CXXRecordDecl* Record) const {

    if (!Record || !Record->isCompleteDefinition()) {
        return false;
    }

    // Destructor should be first if the class has a virtual destructor
    return hasVirtualDestructor(Record);
}
