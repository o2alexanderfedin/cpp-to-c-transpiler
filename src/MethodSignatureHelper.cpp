/**
 * @file MethodSignatureHelper.cpp
 * @brief Implementation of MethodSignatureHelper
 */

#include "../include/MethodSignatureHelper.h"
#include "clang/AST/Type.h"
#include <sstream>

using namespace clang;

std::string MethodSignatureHelper::generateSignature(
    const CXXMethodDecl* Method,
    const std::string& ClassName) {

    std::ostringstream sig;

    // static keyword
    sig << "static ";

    // Return type
    if (isa<CXXConstructorDecl>(Method)) {
        sig << "void";  // Constructors return void in C
    } else if (isa<CXXDestructorDecl>(Method)) {
        sig << "void";  // Destructors return void
    } else {
        sig << getTypeString(Method->getReturnType());
    }

    sig << " ";

    // Method name (mangled for C)
    sig << getMangledName(Method, ClassName);

    // Parameters: always starts with 'this' pointer
    sig << "(";

    // 'this' parameter with proper const qualification
    if (isConstMethod(Method)) {
        sig << "const struct " << ClassName << " *this";
    } else {
        sig << "struct " << ClassName << " *this";
    }

    // Add method parameters
    for (unsigned i = 0; i < Method->getNumParams(); ++i) {
        const ParmVarDecl* param = Method->getParamDecl(i);
        sig << ", ";
        sig << getTypeString(param->getType());

        // Add parameter name if available
        if (!param->getName().empty()) {
            sig << " " << param->getNameAsString();
        } else {
            sig << " arg" << i;
        }
    }

    sig << ")";

    return sig.str();
}

std::string MethodSignatureHelper::getTypeString(QualType Type) {
    // Handle const qualifier
    std::string typeStr;

    if (Type.isConstQualified()) {
        typeStr = "const ";
    }

    // Get base type
    const clang::Type* T = Type.getTypePtr();

    if (T->isVoidType()) {
        typeStr += "void";
    } else if (T->isBooleanType()) {
        typeStr += "int"; // C doesn't have bool, use int
    } else if (T->isIntegerType()) {
        if (T->isSignedIntegerType()) {
            typeStr += "int";
        } else {
            typeStr += "unsigned int";
        }
    } else if (T->isFloatingType()) {
        if (T->isSpecificBuiltinType(BuiltinType::Float)) {
            typeStr += "float";
        } else {
            typeStr += "double";
        }
    } else if (T->isPointerType()) {
        QualType pointeeType = T->getPointeeType();
        typeStr += getTypeString(pointeeType) + " *";
    } else if (T->isReferenceType()) {
        QualType refType = T->getPointeeType();
        typeStr += getTypeString(refType) + " *"; // References become pointers in C
    } else if (const RecordType* RT = T->getAs<RecordType>()) {
        // Class/struct type
        RecordDecl* RD = RT->getDecl();
        typeStr += "struct " + RD->getNameAsString();
    } else {
        // Fallback: use Clang's string representation
        typeStr += Type.getAsString();
    }

    return typeStr;
}

std::string MethodSignatureHelper::getMangledName(
    const CXXMethodDecl* Method,
    const std::string& ClassName) {

    // Constructor naming: ClassName__ctor[_N]
    if (isa<CXXConstructorDecl>(Method)) {
        std::string name = ClassName + "__ctor";
        unsigned numParams = Method->getNumParams();

        // Append parameter count for overload disambiguation
        if (numParams > 0) {
            name += "_" + std::to_string(numParams);
        }

        return name;
    }

    // Destructor naming: ClassName__dtor
    if (isa<CXXDestructorDecl>(Method)) {
        return ClassName + "__dtor";
    }

    // Regular method: ClassName_methodName[_suffix]
    std::string name = ClassName + "_" + Method->getNameAsString();

    // TODO: For now, we don't add overload suffix for regular methods
    // Future enhancement: Add type-based mangling for overloaded methods
    // std::string overloadSuffix = generateOverloadSuffix(Method);
    // if (!overloadSuffix.empty()) {
    //     name += overloadSuffix;
    // }

    return name;
}

bool MethodSignatureHelper::isConstMethod(const CXXMethodDecl* Method) {
    // Constructors and destructors are never const
    if (isa<CXXConstructorDecl>(Method) || isa<CXXDestructorDecl>(Method)) {
        return false;
    }

    // Check if method is const-qualified
    return Method->isConst();
}

std::string MethodSignatureHelper::generateOverloadSuffix(const CXXMethodDecl* Method) {
    // Simple implementation: return empty for now
    // Future enhancement: Generate suffix based on parameter types
    // Example: "_int_float" for method(int, float)
    return "";
}
