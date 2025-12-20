/**
 * @file RvalueRefParamTranslator.cpp
 * @brief Implementation of rvalue reference parameter translation (Story #133)
 */

#include "../include/RvalueRefParamTranslator.h"
#include "clang/AST/Type.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include <sstream>

using namespace clang;

// ============================================================================
// Constructor
// ============================================================================

RvalueRefParamTranslator::RvalueRefParamTranslator(ASTContext& Context)
    : Context(Context) {}

// ============================================================================
// Type Detection
// ============================================================================

bool RvalueRefParamTranslator::isRvalueReference(const QualType& Type) const {
    // Check if type is an rvalue reference (T&&)
    return Type->isRValueReferenceType();
}

bool RvalueRefParamTranslator::isConstRvalueRef(const QualType& Type) const {
    if (!isRvalueReference(Type)) {
        return false;
    }

    // Get the pointee type (the type being referenced)
    QualType pointeeType = Type->getPointeeType();
    return pointeeType.isConstQualified();
}

bool RvalueRefParamTranslator::isPrimitiveType(const QualType& Type) const {
    // Remove reference to get actual type
    QualType actualType = Type;
    if (actualType->isReferenceType()) {
        actualType = actualType->getPointeeType();
    }

    // Check if it's a builtin type (int, float, char, etc.)
    // or a primitive type (not a class/struct)
    return actualType->isBuiltinType() ||
           actualType->isEnumeralType() ||
           actualType->isPointerType();
}

// ============================================================================
// Type Manipulation
// ============================================================================

QualType RvalueRefParamTranslator::getBaseType(const QualType& RvalueRefType) {
    if (!isRvalueReference(RvalueRefType)) {
        return RvalueRefType;
    }

    // Strip the rvalue reference to get the base type
    // For Buffer&&, this returns Buffer
    // For const Buffer&&, this returns const Buffer
    return RvalueRefType->getPointeeType();
}

std::string RvalueRefParamTranslator::getClassName(const QualType& Type) const {
    // Remove reference/pointer qualifiers to get actual type
    QualType actualType = Type;
    if (actualType->isReferenceType()) {
        actualType = actualType->getPointeeType();
    }

    // Get the type as a string
    std::string typeName = actualType.getAsString();

    // For class types, extract just the class name
    if (const RecordType *RT = actualType->getAs<RecordType>()) {
        if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(RT->getDecl())) {
            typeName = RD->getNameAsString();
        }
    }

    return typeName;
}

// ============================================================================
// Type Translation
// ============================================================================

std::string RvalueRefParamTranslator::translateNonRvalueRefType(const QualType& Type) {
    // For non-rvalue-reference types, use standard C type translation
    // This handles lvalue references, pointers, primitives, etc.

    std::string typeName;

    if (Type->isLValueReferenceType()) {
        // Lvalue reference: Buffer& → struct Buffer *
        QualType pointeeType = Type->getPointeeType();
        bool isConst = pointeeType.isConstQualified();

        if (isPrimitiveType(pointeeType)) {
            typeName = pointeeType.getUnqualifiedType().getAsString();
            if (isConst) {
                typeName = "const " + typeName;
            }
            typeName += " *";
        } else {
            std::string className = getClassName(pointeeType);
            if (isConst) {
                typeName = "const struct " + className + " *";
            } else {
                typeName = "struct " + className + " *";
            }
        }
    } else if (Type->isPointerType()) {
        // Pointer type
        typeName = Type.getAsString();
    } else if (isPrimitiveType(Type)) {
        // Primitive type (int, float, etc.)
        typeName = Type.getUnqualifiedType().getAsString();
        if (Type.isConstQualified()) {
            typeName = "const " + typeName;
        }
    } else {
        // Class type by value (rare in parameters, but possible)
        std::string className = getClassName(Type);
        typeName = "struct " + className;
        if (Type.isConstQualified()) {
            typeName = "const " + typeName;
        }
    }

    return typeName;
}

std::string RvalueRefParamTranslator::translateType(const QualType& Type) {
    // Check if this is an rvalue reference
    if (!isRvalueReference(Type)) {
        // Delegate to existing type translation for non-rvalue-refs
        return translateNonRvalueRefType(Type);
    }

    // Get the base type (without &&)
    QualType baseType = getBaseType(Type);
    bool isConst = isConstRvalueRef(Type);

    // Check if it's a primitive type
    if (isPrimitiveType(baseType)) {
        // For primitives, pass by value in C (implementation choice)
        // int&& → int
        std::string typeName = baseType.getUnqualifiedType().getAsString();
        if (isConst) {
            typeName = "const " + typeName;
        }
        return typeName;
    }

    // For class types, translate to pointer
    // Buffer&& → struct Buffer *
    // const Buffer&& → const struct Buffer *
    std::string className = getClassName(baseType);

    std::ostringstream result;
    if (isConst) {
        result << "const struct " << className << " *";
    } else {
        result << "struct " << className << " *";
    }

    return result.str();
}

// ============================================================================
// Parameter Translation
// ============================================================================

std::string RvalueRefParamTranslator::translateParameter(const ParmVarDecl* Param) {
    if (!Param) {
        return "";
    }

    // Get parameter type and name
    QualType paramType = Param->getType();
    std::string paramName = Param->getNameAsString();

    // Translate the type
    std::string cType = translateType(paramType);

    // Combine type and name
    // Handle cases where type already ends with *
    std::ostringstream result;
    result << cType;

    // Add space before name if type doesn't end with *
    if (!cType.empty() && cType.back() != '*') {
        result << " ";
    }

    result << paramName;

    return result.str();
}

// ============================================================================
// Function Signature Translation
// ============================================================================

std::string RvalueRefParamTranslator::translateFunctionSignature(const FunctionDecl* Func) {
    if (!Func) {
        return "";
    }

    std::ostringstream signature;

    // Translate return type
    QualType returnType = Func->getReturnType();
    std::string cReturnType = translateType(returnType);
    signature << cReturnType;

    // Add space before function name if return type doesn't end with *
    if (!cReturnType.empty() && cReturnType.back() != '*') {
        signature << " ";
    }

    // Add function name
    signature << Func->getNameAsString();

    // Add parameters
    signature << "(";

    unsigned numParams = Func->getNumParams();
    for (unsigned i = 0; i < numParams; ++i) {
        if (i > 0) {
            signature << ", ";
        }

        const ParmVarDecl* param = Func->getParamDecl(i);
        signature << translateParameter(param);
    }

    // Handle void parameter list
    if (numParams == 0) {
        signature << "void";
    }

    signature << ")";

    return signature.str();
}
