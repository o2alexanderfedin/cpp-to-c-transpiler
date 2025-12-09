/**
 * @file VtableGenerator.cpp
 * @brief Implementation of VtableGenerator
 */

#include "../include/VtableGenerator.h"
#include "../include/OverrideResolver.h"
#include "clang/AST/DeclCXX.h"
#include <sstream>
#include <map>
#include <functional>

using namespace clang;

VtableGenerator::VtableGenerator(ASTContext& Context, VirtualMethodAnalyzer& Analyzer,
                                  OverrideResolver* Resolver)
    : Context(Context), Analyzer(Analyzer), Resolver(Resolver) {}

std::string VtableGenerator::generateVtableStruct(const CXXRecordDecl* Record) {
    if (!Record || !Analyzer.isPolymorphic(Record)) {
        return ""; // Not polymorphic, no vtable needed
    }

    std::ostringstream code;
    std::string className = Record->getNameAsString();

    // Generate vtable struct
    code << "struct " << className << "_vtable {\n";

    // Get methods in vtable order
    auto methods = getVtableMethodOrder(Record);

    // Generate function pointers for each method
    for (auto* method : methods) {
        code << "    " << generateFunctionPointer(method, className) << ";\n";
    }

    code << "};\n";

    return code.str();
}

std::vector<CXXMethodDecl*> VtableGenerator::getVtableMethodOrder(const CXXRecordDecl* Record) {
    if (!Record) {
        return {};
    }

    // Story #170: Use OverrideResolver if available for proper override resolution
    if (Resolver) {
        return Resolver->resolveVtableLayout(Record);
    }

    // Legacy fallback: basic implementation (kept for backwards compatibility)
    std::vector<CXXMethodDecl*> methods;

    // Collect all virtual methods including inherited ones
    // Use a map to track methods by name (for overrides)
    std::map<std::string, CXXMethodDecl*> methodMap;
    CXXDestructorDecl* destructor = nullptr;

    // Walk the inheritance hierarchy
    std::function<void(const CXXRecordDecl*)> collectMethods =
        [&](const CXXRecordDecl* R) {
            if (!R) return;

            // Process base classes first
            for (const auto& Base : R->bases()) {
                if (const auto* BaseRecord = Base.getType()->getAsCXXRecordDecl()) {
                    collectMethods(BaseRecord);
                }
            }

            // Process methods in this class
            for (auto* method : R->methods()) {
                if (!method->isVirtual()) continue;

                if (isa<CXXDestructorDecl>(method)) {
                    // Always use the most derived destructor
                    destructor = cast<CXXDestructorDecl>(method);
                } else {
                    // For regular methods, derived versions override base versions
                    std::string methodName = method->getNameAsString();
                    methodMap[methodName] = method;
                }
            }
        };

    collectMethods(Record);

    // Add destructor first if present
    if (destructor) {
        methods.push_back(destructor);
    }

    // Add virtual methods in order
    for (const auto& pair : methodMap) {
        methods.push_back(pair.second);
    }

    return methods;
}

std::string VtableGenerator::generateFunctionPointer(const CXXMethodDecl* Method,
                                                      const std::string& ClassName) {
    std::ostringstream ptr;

    // Return type
    QualType returnType = Method->getReturnType();
    ptr << getTypeString(returnType) << " ";

    // Function pointer name
    if (isa<CXXDestructorDecl>(Method)) {
        ptr << "(*destructor)";
    } else {
        ptr << "(*" << Method->getNameAsString() << ")";
    }

    // Parameters: always starts with 'this' pointer
    ptr << "(struct " << ClassName << " *this";

    // Add method parameters
    for (unsigned i = 0; i < Method->getNumParams(); ++i) {
        const ParmVarDecl* param = Method->getParamDecl(i);
        ptr << ", " << getTypeString(param->getType());

        // Add parameter name if available
        if (!param->getName().empty()) {
            ptr << " " << param->getNameAsString();
        } else {
            ptr << " arg" << i;
        }
    }

    ptr << ")";

    return ptr.str();
}

std::string VtableGenerator::getTypeString(QualType Type) {
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
        // Fallback for unknown types
        typeStr += "void";
    }

    return typeStr;
}
