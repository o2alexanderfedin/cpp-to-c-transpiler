/**
 * @file NameMangler.cpp
 * @brief Implementation of NameMangler class
 *
 * Story #18: Basic Name Mangling
 * Story #65: Namespace-Aware Name Mangling
 * Phase 48: Anonymous Namespace Support
 */

#include "NameMangler.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/Support/Path.h"
#include <algorithm>

using namespace clang;

std::string NameMangler::mangleName(CXXMethodDecl *MD) {
    // Build base name: ClassName_methodName
    std::string baseName = MD->getParent()->getName().str() + "_" + MD->getName().str();

    // Phase 40 (Bug Fix): Always append parameter types for cross-file consistency
    // This ensures method names are the same whether generated from definition or call site
    // Example: Vector3D::dot(const Vector3D&) -> Vector3D_dot_const_Vector3D_ref
    std::string mangledName = baseName;
    for (ParmVarDecl *Param : MD->parameters()) {
        std::string paramType = getSimpleTypeName(Param->getType());
        mangledName += "_" + paramType;
    }

    // If no parameters, use base name (for methods like getX(), clear(), etc.)
    if (MD->param_size() == 0) {
        mangledName = baseName;
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
    // Phase 40 (Bug Fix): Handle reference types FIRST before checking const
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

std::string NameMangler::getAnonymousNamespaceID(NamespaceDecl *ND) {
    // Phase 48: Generate unique ID for anonymous namespace
    // Pattern: _anon_<basename>_<line>
    // Example: _anon_utils_cpp_42 for line 42 in utils.cpp

    SourceLocation Loc = ND->getLocation();
    SourceManager &SM = Ctx.getSourceManager();

    // Get file name
    llvm::StringRef FileName = SM.getFilename(Loc);
    std::string FileBaseName = llvm::sys::path::filename(FileName).str();

    // Get line number
    unsigned LineNum = SM.getSpellingLineNumber(Loc);

    // Generate unique ID
    std::string uniqueId = "_anon_" + FileBaseName + "_" + std::to_string(LineNum);

    // Replace special characters in filename to make valid C identifier
    std::replace(uniqueId.begin(), uniqueId.end(), '.', '_');
    std::replace(uniqueId.begin(), uniqueId.end(), '-', '_');
    std::replace(uniqueId.begin(), uniqueId.end(), ' ', '_');

    return uniqueId;
}

std::vector<std::string> NameMangler::extractNamespaceHierarchy(Decl *D) {
    // Build namespace hierarchy from outermost to innermost
    // Example: ns1::ns2::func returns {"ns1", "ns2"}
    // Phase 48: Enhanced with anonymous namespace support
    // Example: namespace { func; } returns {"_anon_file_cpp_42"}
    std::vector<std::string> namespaces;

    DeclContext *DC = D->getDeclContext();
    while (DC) {
        if (auto *ND = dyn_cast<NamespaceDecl>(DC)) {
            if (!ND->isAnonymousNamespace()) {
                // Named namespace: use name directly
                namespaces.push_back(ND->getName().str());
            } else {
                // Anonymous namespace: generate unique ID
                std::string uniqueId = getAnonymousNamespaceID(ND);
                namespaces.push_back(uniqueId);
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
    // Note: Skip 'this' parameter (implicit in C++ methods) for cleaner names
    std::string mangledName = baseName;
    for (ParmVarDecl *Param : FD->parameters()) {
        // Skip 'this' parameter - it's implicit in C++ and shouldn't affect overload resolution
        if (Param->getName() == "this") {
            continue;
        }
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

// ============================================================================
// Phase 49: Static Data Member Support
// ============================================================================

std::string NameMangler::mangleStaticMember(CXXRecordDecl *RD, VarDecl *VD) {
    // Extract namespace hierarchy
    std::vector<std::string> namespaces = extractNamespaceHierarchy(RD);

    // Build fully qualified class name with namespaces and nested classes
    std::string qualifiedClassName;

    // Add namespace prefix
    for (const auto &ns : namespaces) {
        qualifiedClassName += ns + "__";
    }

    // Add class hierarchy (handle nested classes)
    // Walk up the parent chain to build: Outer__Inner__...
    std::vector<std::string> classHierarchy;
    const DeclContext *DC = RD;
    while (DC && !DC->isTranslationUnit()) {
        if (auto *parentRecord = dyn_cast<CXXRecordDecl>(DC)) {
            classHierarchy.push_back(parentRecord->getNameAsString());
        }
        DC = DC->getParent();
    }

    // Reverse to get outermost-to-innermost order
    std::reverse(classHierarchy.begin(), classHierarchy.end());

    // Build class hierarchy: Outer__Inner__...
    for (size_t i = 0; i < classHierarchy.size(); ++i) {
        qualifiedClassName += classHierarchy[i];
        if (i < classHierarchy.size() - 1) {
            qualifiedClassName += "__";
        }
    }

    // Add member name with double underscore separator
    // Pattern: [ns__]Class__member or [ns__]Outer__Inner__member
    std::string mangledName = qualifiedClassName + "__" + VD->getNameAsString();

    return mangledName;
}
