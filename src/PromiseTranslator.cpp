/**
 * @file PromiseTranslator.cpp
 * @brief Implementation of PromiseTranslator (Story #105)
 */

#include "../include/PromiseTranslator.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/DeclCXX.h"
#include <sstream>

using namespace clang;

PromiseTranslator::PromiseTranslator(ASTContext& Context)
    : Context(Context) {}

CXXRecordDecl* PromiseTranslator::extractPromiseType(const CXXRecordDecl* returnType) {
    if (!returnType || !returnType->isCompleteDefinition()) {
        return nullptr;
    }

    // Look for nested promise_type class
    for (auto *D : returnType->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "promise_type" && RD->isCompleteDefinition()) {
                return RD;
            }
        }
        // Also check type aliases
        if (auto *TD = dyn_cast<TypedefNameDecl>(D)) {
            if (TD->getNameAsString() == "promise_type") {
                if (auto *tagDecl = TD->getUnderlyingType()->getAsCXXRecordDecl()) {
                    return tagDecl;
                }
            }
        }
    }

    return nullptr;
}

std::string PromiseTranslator::generatePromiseStruct(const CXXRecordDecl* returnType) {
    if (!returnType) {
        return "";
    }

    auto *promiseType = extractPromiseType(returnType);
    if (!promiseType) {
        return "";
    }

    std::ostringstream code;
    std::string structName = getPromiseStructName(returnType);

    code << "// Promise structure for " << returnType->getNameAsString() << "\n";
    code << "struct " << structName << " {\n";

    // Translate data members
    std::string members = translatePromiseMembers(promiseType);
    if (!members.empty()) {
        code << members;
    } else {
        code << "    // No data members\n";
    }

    code << "};\n";

    return code.str();
}

std::string PromiseTranslator::translateGetReturnObject(const CXXRecordDecl* returnType) {
    if (!returnType) {
        return "";
    }

    auto *promiseType = extractPromiseType(returnType);
    if (!promiseType) {
        return "";
    }

    std::ostringstream code;
    std::string funcName = returnType->getNameAsString() + "_promise_get_return_object";

    code << "// get_return_object for " << returnType->getNameAsString() << "\n";
    code << "void " << funcName << "(struct " << getPromiseStructName(returnType) << "* promise) {\n";
    code << "    // Initialize return object\n";
    code << "}\n";

    return code.str();
}

std::string PromiseTranslator::translateYieldValue(const CXXRecordDecl* returnType) {
    if (!returnType) {
        return "";
    }

    auto *promiseType = extractPromiseType(returnType);
    if (!promiseType) {
        return "";
    }

    // Check if promise_type has yield_value method
    bool hasYieldValue = false;
    for (auto *M : promiseType->methods()) {
        if (M->getNameAsString() == "yield_value") {
            hasYieldValue = true;
            break;
        }
    }

    if (!hasYieldValue) {
        return "";
    }

    std::ostringstream code;
    std::string funcName = returnType->getNameAsString() + "_promise_yield_value";

    code << "// yield_value for " << returnType->getNameAsString() << "\n";
    code << "void " << funcName << "(struct " << getPromiseStructName(returnType) << "* promise, int value) {\n";
    code << "    promise->value = value;\n";
    code << "}\n";

    return code.str();
}

std::string PromiseTranslator::translateReturnVoid(const CXXRecordDecl* returnType) {
    if (!returnType) {
        return "";
    }

    auto *promiseType = extractPromiseType(returnType);
    if (!promiseType) {
        return "";
    }

    // return_void is often a no-op in C
    std::ostringstream code;
    std::string funcName = returnType->getNameAsString() + "_promise_return_void";

    code << "// return_void for " << returnType->getNameAsString() << "\n";
    code << "void " << funcName << "(struct " << getPromiseStructName(returnType) << "* promise) {\n";
    code << "    // No-op in C (no exceptions)\n";
    code << "}\n";

    return code.str();
}

std::string PromiseTranslator::translateUnhandledException(const CXXRecordDecl* returnType) {
    if (!returnType) {
        return "";
    }

    auto *promiseType = extractPromiseType(returnType);
    if (!promiseType) {
        return "";
    }

    // unhandled_exception is a no-op in C (no exceptions)
    std::ostringstream code;
    std::string funcName = returnType->getNameAsString() + "_promise_unhandled_exception";

    code << "// unhandled_exception for " << returnType->getNameAsString() << "\n";
    code << "void " << funcName << "(struct " << getPromiseStructName(returnType) << "* promise) {\n";
    code << "    // No-op in C (no exceptions)\n";
    code << "}\n";

    return code.str();
}

std::string PromiseTranslator::getPromiseStructName(const CXXRecordDecl* returnType) {
    if (!returnType) {
        return "";
    }
    return returnType->getNameAsString() + "_promise";
}

std::string PromiseTranslator::translatePromiseMembers(const CXXRecordDecl* promiseType) {
    if (!promiseType) {
        return "";
    }

    std::ostringstream code;

    // Extract data members (fields)
    for (auto *F : promiseType->fields()) {
        QualType fieldType = F->getType();
        std::string typeName = fieldType.getAsString();
        std::string fieldName = F->getNameAsString();

        code << "    " << typeName << " " << fieldName << ";\n";
    }

    return code.str();
}
