/**
 * @file NameMangler.cpp
 * @brief Implementation of NameMangler class
 *
 * Story #18: Basic Name Mangling
 * Story #65: Namespace-Aware Name Mangling
 */

#include "NameMangler.h"
#include <algorithm>

using namespace clang;

std::string NameMangler::mangleName(CXXMethodDecl *MD) {
    // Build base name: ClassName_methodName
    std::string baseName = MD->getParent()->getName().str() + "_" + MD->getName().str();

    // Check if base name is unique (no overloading)
    if (usedNames.find(baseName) == usedNames.end()) {
        usedNames.insert(baseName);
        return baseName;
    }

    // Handle overload: append parameter types
    std::string mangledName = baseName;
    for (ParmVarDecl *Param : MD->parameters()) {
        mangledName += "_" + getSimpleTypeName(Param->getType());
    }

    usedNames.insert(mangledName);
    return mangledName;
}

std::string NameMangler::mangleConstructor(CXXConstructorDecl *CD) {
    // Base name: ClassName__ctor
    std::string baseName = CD->getParent()->getName().str() + "__ctor";

    // Check if base name is unique
    if (usedNames.find(baseName) == usedNames.end()) {
        usedNames.insert(baseName);
        return baseName;
    }

    // Handle overloaded constructors: append parameter count
    std::string mangledName = baseName + "_" + std::to_string(CD->getNumParams());

    usedNames.insert(mangledName);
    return mangledName;
}

std::string NameMangler::mangleDestructor(CXXDestructorDecl *DD) {
    // Destructor name: ClassName__dtor
    // Note: Destructors cannot be overloaded, so no suffix needed
    std::string mangledName = DD->getParent()->getName().str() + "__dtor";

    usedNames.insert(mangledName);
    return mangledName;
}

std::string NameMangler::getSimpleTypeName(QualType T) {
    // Story #66: Encode const qualification and reference types explicitly
    std::string result;

    // Check for const qualification before removing it
    bool isConst = T.isConstQualified();
    if (isConst) {
        result += "const_";
    }

    // Check for reference types
    bool isReference = false;
    bool isRValueRef = false;
    if (T->isLValueReferenceType()) {
        isReference = true;
        T = T.getNonReferenceType();
    } else if (T->isRValueReferenceType()) {
        isRValueRef = true;
        T = T.getNonReferenceType();
    }

    // Remove remaining qualifiers
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
        result += "ptr";
    }
    // Handle record types (struct/class)
    else if (T->isRecordType()) {
        if (auto *RD = T->getAsRecordDecl()) {
            result += RD->getName().str();
        } else {
            result += "record";
        }
    }
    // Fallback: use full type string
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

// ============================================================================
// Story #65: Namespace-Aware Name Mangling
// ============================================================================

std::vector<std::string> NameMangler::extractNamespaceHierarchy(Decl *D) {
    // Build namespace hierarchy from outermost to innermost
    // Example: ns1::ns2::func returns {"ns1", "ns2"}
    std::vector<std::string> namespaces;

    DeclContext *DC = D->getDeclContext();
    while (DC) {
        if (auto *ND = dyn_cast<NamespaceDecl>(DC)) {
            // Skip anonymous namespaces
            if (!ND->isAnonymousNamespace()) {
                namespaces.push_back(ND->getName().str());
            }
        }
        DC = DC->getParent();
    }

    // Reverse to get outermost-to-innermost order
    std::reverse(namespaces.begin(), namespaces.end());
    return namespaces;
}

std::string NameMangler::mangleClassName(CXXRecordDecl *RD) {
    // Extract namespace hierarchy
    std::vector<std::string> namespaces = extractNamespaceHierarchy(RD);

    // Build mangled name: ns1_ns2_ClassName
    std::string mangledName;
    for (const auto &ns : namespaces) {
        mangledName += ns + "_";
    }
    mangledName += RD->getName().str();

    return mangledName;
}

std::string NameMangler::mangleMethodName(CXXMethodDecl *MD) {
    // Extract namespace hierarchy
    std::vector<std::string> namespaces = extractNamespaceHierarchy(MD->getParent());

    // Build mangled name: ns1_ns2_ClassName_methodName
    std::string mangledName;
    for (const auto &ns : namespaces) {
        mangledName += ns + "_";
    }
    mangledName += MD->getParent()->getName().str() + "_" + MD->getName().str();

    return mangledName;
}

std::string NameMangler::mangleFunctionName(FunctionDecl *FD) {
    // Extract namespace hierarchy
    std::vector<std::string> namespaces = extractNamespaceHierarchy(FD);

    // Build mangled name: ns1_ns2_funcName
    std::string mangledName;
    for (const auto &ns : namespaces) {
        mangledName += ns + "_";
    }
    mangledName += FD->getName().str();

    return mangledName;
}
