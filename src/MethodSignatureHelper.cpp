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
    // Phase 35-02 CRITICAL BUG FIX: Properly handle reference types
    // References MUST be converted to pointers BEFORE any other processing

    const clang::Type* T = Type.getTypePtr();

    // Phase 35-02: Check if this is a reference type FIRST (before removing qualifiers)
    // This is CRITICAL: const T& is different from const T
    if (const ReferenceType* RT = dyn_cast<ReferenceType>(T)) {
        // Get the pointee type (what the reference refers to)
        QualType PointeeType = RT->getPointeeType();

        // References become pointers in C
        // Recursively process the pointee type, then add pointer
        return getTypeString(PointeeType) + " *";
    }

    // For const types, we need to handle the qualifier separately
    const bool isConst = Type.isConstQualified();
    const bool isVolatile = Type.isVolatileQualified();

    // Get base type without qualifiers for caching
    QualType BaseType = Type.getUnqualifiedType();
    const clang::Type* BaseT = BaseType.getTypePtr();

    // Check cache for the base type (without const/volatile)
    auto it = typeStringCache.find(BaseT);
    if (it != typeStringCache.end()) {
        // Cache hit - return cached string with qualifiers if needed
        std::string result;
        if (isConst) result += "const ";
        if (isVolatile) result += "volatile ";
        result += it->second;
        return result;
    }

    // Cache miss - compute type string
    std::string baseTypeStr;

    if (BaseT->isVoidType()) {
        baseTypeStr = "void";
    } else if (BaseT->isBooleanType()) {
        baseTypeStr = "int"; // C doesn't have bool, use int
    } else if (BaseT->isIntegerType()) {
        if (BaseT->isSignedIntegerType()) {
            baseTypeStr = "int";
        } else {
            baseTypeStr = "unsigned int";
        }
    } else if (BaseT->isFloatingType()) {
        if (BaseT->isSpecificBuiltinType(BuiltinType::Float)) {
            baseTypeStr = "float";
        } else {
            baseTypeStr = "double";
        }
    } else if (BaseT->isPointerType()) {
        QualType pointeeType = BaseT->getPointeeType();
        baseTypeStr = getTypeString(pointeeType) + " *";
    } else if (const RecordType* RT = BaseT->getAs<RecordType>()) {
        // Class/struct type
        RecordDecl* RD = RT->getDecl();
        baseTypeStr = "struct " + RD->getNameAsString();
    } else {
        // Fallback: use Clang's string representation
        // Phase 35-02: This should NEVER be reached for reference types now
        baseTypeStr = Type.getAsString();
    }

    // Cache the base type string
    typeStringCache[BaseT] = baseTypeStr;

    // Return with qualifiers if needed
    std::string result;
    if (isConst) result += "const ";
    if (isVolatile) result += "volatile ";
    result += baseTypeStr;
    return result;
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

    // Phase 40 (Bug Fix): Always add parameter type suffix for cross-file consistency
    // This ensures method names match whether generated from definition or call site
    std::string overloadSuffix = generateOverloadSuffix(Method);
    if (!overloadSuffix.empty()) {
        name += overloadSuffix;
    }

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
    // Phase 40 (Bug Fix): Generate suffix based on parameter types
    // Example: dot(const Vector3D&) -> "_const_Vector3D_ref"
    // Example: add(int, float) -> "_int_float"

    if (Method->param_size() == 0) {
        return "";  // No parameters, no suffix
    }

    std::string suffix;
    for (unsigned i = 0; i < Method->getNumParams(); ++i) {
        const ParmVarDecl* param = Method->getParamDecl(i);
        QualType paramType = param->getType();

        suffix += "_" + getSimpleTypeName(paramType);
    }

    return suffix;
}

// Helper function to generate simple type names for mangling
std::string MethodSignatureHelper::getSimpleTypeName(QualType T) {
    std::string result;

    // CRITICAL: Handle reference types FIRST (before checking const)
    // For const T&, the const is on the pointee, not the reference itself
    bool isReference = false;
    bool isRValueRef = false;
    if (T->isLValueReferenceType()) {
        isReference = true;
        T = T.getNonReferenceType();  // Now T is the pointee type
    } else if (T->isRValueReferenceType()) {
        isRValueRef = true;
        T = T.getNonReferenceType();
    }

    // NOW check for const qualification (after stripping reference)
    bool isConst = T.isConstQualified();
    if (isConst) {
        result += "const_";
    }

    // Remove const/volatile qualifiers for type matching
    T = T.getUnqualifiedType();

    // Handle integer types
    if (T->isIntegerType()) {
        result += "int";
    }
    // Handle floating point types
    else if (T->isFloatingType()) {
        result += "float";
    }
    // Handle pointer types
    else if (T->isPointerType()) {
        QualType pointee = T->getPointeeType();
        result += getSimpleTypeName(pointee) + "_ptr";
    }
    // Handle record types (struct/class)
    else if (T->isRecordType()) {
        if (auto *RD = T->getAsRecordDecl()) {
            result += RD->getName().str();
        } else {
            result += "record";
        }
    }
    // Fallback
    else {
        result += T.getAsString();
    }

    // Append reference suffix
    if (isReference) {
        result += "_ref";
    } else if (isRValueRef) {
        result += "_rref";
    }

    return result;
}
