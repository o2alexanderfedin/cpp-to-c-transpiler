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
    // Handle pointer types - recursively encode pointee type (like Itanium C++ ABI)
    // This preserves type information and fixes overload resolution
    // Example: int* → "int_ptr", char* → "char_ptr" (not just "ptr")
    else if (T->isPointerType()) {
        QualType pointee = T->getPointeeType();
        result += getSimpleTypeName(pointee) + "_ptr";  // Recursive encoding!
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
    // Prompt #031: extern "C" and Calling Convention Support
    // CRITICAL: Check for extern "C" linkage BEFORE any mangling
    // extern "C" functions must have unmangled names to preserve C ABI
    if (FD->isExternC()) {
        return FD->getName().str();  // Return unmangled name for C linkage
    }

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

// ============================================================================
// Phase 8: Standalone Function Translation (v2.1.0)
// ============================================================================

std::string NameMangler::mangleStandaloneFunction(FunctionDecl *FD) {
    // Special case 1: main() function - never mangle
    if (FD->getName() == "main") {
        return "main";
    }

    // Special case 2: extern "C" functions - preserve C linkage
    if (FD->isExternC()) {
        return FD->getName().str();
    }

    // Extract namespace hierarchy for base name
    std::vector<std::string> namespaces = extractNamespaceHierarchy(FD);

    // Build base name with namespaces
    std::string baseName;
    for (const auto &ns : namespaces) {
        baseName += ns + "_";
    }
    baseName += FD->getName().str();

    // Check if base name is unique (no overloading)
    if (usedNames.find(baseName) == usedNames.end()) {
        usedNames.insert(baseName);
        return baseName;
    }

    // Handle overload: append parameter types
    // Pattern: functionName_paramType1_paramType2_...
    std::string mangledName = baseName;
    for (ParmVarDecl *Param : FD->parameters()) {
        mangledName += "_" + getSimpleTypeName(Param->getType());
    }

    // Handle case where even with param types, name collides (multiple overloads)
    // In this case, append a counter
    std::string finalName = mangledName;
    int counter = 1;
    while (usedNames.find(finalName) != usedNames.end()) {
        finalName = mangledName + "_" + std::to_string(counter);
        counter++;
    }

    usedNames.insert(finalName);
    return finalName;
}
