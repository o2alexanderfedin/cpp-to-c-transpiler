/**
 * @file MethodSignatureHelper.cpp
 * @brief Implementation of MethodSignatureHelper
 */

#include "../include/MethodSignatureHelper.h"
#include "clang/AST/Type.h"
#include <sstream>
#include <unordered_map>

using namespace clang;

// Phase 31-04: Performance optimization caches
namespace {
    // Cache for type strings to avoid redundant AST queries
    std::unordered_map<const clang::Type*, std::string> typeStringCache;
}

void MethodSignatureHelper::clearCaches() {
    typeStringCache.clear();
}

std::string MethodSignatureHelper::generateSignature(
    const CXXMethodDecl* Method,
    const std::string& ClassName) {

    // Phase 31-04: Pre-allocate string buffer to reduce reallocations
    // Typical signature: ~80-120 characters
    std::string sig;
    sig.reserve(128);

    // Phase 31-04: Cache method properties to avoid repeated AST queries
    const bool isConstructor = isa<CXXConstructorDecl>(Method);
    const bool isDestructor = isa<CXXDestructorDecl>(Method);
    const bool isConst = isConstMethod(Method);
    const unsigned numParams = Method->getNumParams();

    // static keyword
    sig += "static ";

    // Return type
    if (isConstructor || isDestructor) {
        sig += "void";  // Constructors/destructors return void in C
    } else {
        sig += getTypeString(Method->getReturnType());
    }

    sig += " ";

    // Method name (mangled for C)
    sig += getMangledName(Method, ClassName);

    // Parameters: always starts with 'this' pointer
    sig += "(";

    // 'this' parameter with proper const qualification
    if (isConst) {
        sig += "const struct ";
        sig += ClassName;
        sig += " *this";
    } else {
        sig += "struct ";
        sig += ClassName;
        sig += " *this";
    }

    // Add method parameters
    for (unsigned i = 0; i < numParams; ++i) {
        const ParmVarDecl* param = Method->getParamDecl(i);
        sig += ", ";
        sig += getTypeString(param->getType());

        // Add parameter name if available
        if (!param->getName().empty()) {
            sig += " ";
            sig += param->getNameAsString();
        } else {
            sig += " arg";
            sig += std::to_string(i);
        }
    }

    sig += ")";

    return sig;
}

std::string MethodSignatureHelper::getTypeString(QualType Type) {
    // Phase 31-04: Check cache first for non-const types
    const clang::Type* T = Type.getTypePtr();

    // For const types, we need to handle the qualifier separately
    const bool isConst = Type.isConstQualified();

    // Check cache for the base type (without const)
    auto it = typeStringCache.find(T);
    if (it != typeStringCache.end()) {
        // Cache hit - return cached string with const prefix if needed
        if (isConst) {
            return "const " + it->second;
        }
        return it->second;
    }

    // Cache miss - compute type string
    std::string baseTypeStr;

    if (T->isVoidType()) {
        baseTypeStr = "void";
    } else if (T->isBooleanType()) {
        baseTypeStr = "int"; // C doesn't have bool, use int
    } else if (T->isIntegerType()) {
        if (T->isSignedIntegerType()) {
            baseTypeStr = "int";
        } else {
            baseTypeStr = "unsigned int";
        }
    } else if (T->isFloatingType()) {
        if (T->isSpecificBuiltinType(BuiltinType::Float)) {
            baseTypeStr = "float";
        } else {
            baseTypeStr = "double";
        }
    } else if (T->isPointerType()) {
        QualType pointeeType = T->getPointeeType();
        baseTypeStr = getTypeString(pointeeType) + " *";
    } else if (T->isReferenceType()) {
        QualType refType = T->getPointeeType();
        baseTypeStr = getTypeString(refType) + " *"; // References become pointers in C
    } else if (const RecordType* RT = T->getAs<RecordType>()) {
        // Class/struct type
        RecordDecl* RD = RT->getDecl();
        baseTypeStr = "struct " + RD->getNameAsString();
    } else {
        // Fallback: use Clang's string representation
        baseTypeStr = Type.getAsString();
    }

    // Cache the base type string
    typeStringCache[T] = baseTypeStr;

    // Return with const prefix if needed
    if (isConst) {
        return "const " + baseTypeStr;
    }
    return baseTypeStr;
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
