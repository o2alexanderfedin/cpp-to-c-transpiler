/**
 * @file NameMangler.cpp
 * @brief Implementation of NameMangler class
 *
 * Story #18: Basic Name Mangling
 * Story #65: Namespace-Aware Name Mangling
 * Phase 2: OverloadRegistry Integration
 * Phase 48: Anonymous Namespace Support
 *
 * Key Changes (Phase 2):
 * - Removed per-instance usedNames set
 * - All mangling uses OverloadRegistry for cross-file consistency
 * - Deterministic ordering ensures same input → same output
 */

#include "NameMangler.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/Support/Path.h"
#include <algorithm>

using namespace clang;
using namespace cpptoc;

std::string NameMangler::mangleName(CXXMethodDecl *MD) {
    // Phase 2: Registry-backed mangling for cross-file consistency
    // Phase 53: Handle operator methods with proper sanitization

    std::string methodName;
    if (MD->isOverloadedOperator()) {
        // Use sanitized operator name instead of raw symbols
        methodName = sanitizeOperatorName(MD->getOverloadedOperator());
    } else {
        // Regular method - use getName().str()
        methodName = MD->getName().str();
    }

    // Build base name: ClassName_methodName
    std::string baseName = MD->getParent()->getName().str() + "_" + methodName;

    // Always append parameter types for cross-file consistency
    // This ensures method names are the same whether generated from definition or call site
    // Example: Vector3D::dot(const Vector3D&) -> Vector3D_dot_const_Vector3D_ref
    // Example: Array::operator[](int) -> Array_operator_indexer_int
    std::string mangledName = baseName;
    for (ParmVarDecl *Param : MD->parameters()) {
        std::string paramType = getSimpleTypeName(Param->getType());
        mangledName += "_" + paramType;
    }

    // If no parameters, use base name (for methods like getX(), clear(), etc.)
    if (MD->param_size() == 0) {
        mangledName = baseName;
    }

    // Phase 53: Add prefix/postfix distinguisher for increment/decrement
    if (MD->isOverloadedOperator() &&
        (MD->getOverloadedOperator() == OO_PlusPlus ||
         MD->getOverloadedOperator() == OO_MinusMinus)) {
        // Postfix has dummy int parameter (already encoded above)
        // Prefix has no parameters - add explicit suffix for clarity
        if (MD->getNumParams() == 0) {
            mangledName += "_prefix";
        } else {
            mangledName += "_postfix";
        }
    }

    // Register with global registry for cross-file tracking
    registry_.registerOverload(baseName, MD, mangledName);

    return mangledName;
}

std::string NameMangler::mangleConstructor(CXXConstructorDecl *CD) {
    // Phase 2: Registry-backed constructor mangling
    // Base name: ClassName__ctor
    std::string baseName = CD->getParent()->getName().str() + "__ctor";

    // Check if already registered (may be called multiple times for same constructor)
    std::string existing = registry_.getMangledName(baseName, CD);
    if (!existing.empty()) {
        return existing;
    }

    // Determine mangled name based on existing overloads
    std::string mangledName;
    if (!registry_.hasMultipleOverloads(baseName) && registry_.countOverloads(baseName) == 0) {
        // First constructor - use simple name
        mangledName = baseName;
    } else {
        // Handle overloaded constructors: append parameter count
        mangledName = baseName + "_" + std::to_string(CD->getNumParams());
    }

    // Register with global registry
    registry_.registerOverload(baseName, CD, mangledName);

    return mangledName;
}

std::string NameMangler::mangleDestructor(CXXDestructorDecl *DD) {
    // Phase 2: Registry-backed destructor mangling
    // Destructor name: ClassName__dtor
    // Note: Destructors cannot be overloaded, so no suffix needed
    std::string baseName = DD->getParent()->getName().str() + "__dtor";
    std::string mangledName = baseName;

    // Register with global registry (destructors not overloaded, but still track)
    registry_.registerOverload(baseName, DD, mangledName);

    return mangledName;
}

// ============================================================================
// Phase 53: Conversion Operator Mangling
// ============================================================================

std::string NameMangler::mangleConversionOperator(CXXConversionDecl *CD) {
    if (!CD) {
        return "";
    }

    // Get parent class
    const CXXRecordDecl* ClassDecl = CD->getParent();
    if (!ClassDecl) {
        return "operator_to_unknown";
    }

    // Extract namespace hierarchy for class name
    std::vector<std::string> hierarchy = extractNamespaceHierarchy(const_cast<CXXRecordDecl*>(ClassDecl));

    // Build class name with namespace prefix
    std::string className;
    for (const auto &item : hierarchy) {
        if (item.substr(0, 3) == "ns:") {
            className += item.substr(3) + "_";
        } else if (item.substr(0, 4) == "rec:") {
            className += item.substr(4) + "__";
        }
    }
    className += ClassDecl->getNameAsString();

    // Get conversion target type
    clang::QualType ConvType = CD->getConversionType();
    std::string TargetType = ConvType.getAsString();

    // Sanitize target type name for C identifier
    // Pattern: operator_to_[targetType]
    std::string opName = "operator_to_";
    for (char c : TargetType) {
        if (isalnum(c)) {
            opName += c;
        } else if (c == ' ' || c == '*' || c == '&' || c == ':') {
            opName += '_';
        }
        // Skip other special characters
    }

    // Add const qualifier if present
    if (CD->isConst()) {
        opName += "_const";
    }

    // Build final mangled name: ClassName_operator_to_targetType[_const]
    std::string mangledName = className + "_" + opName;

    // Register with global registry
    registry_.registerOverload(className + "_conversion", CD, mangledName);

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
    // Phase 3: Enhanced with nested struct/class support
    // Example: Outer::Inner returns {"Outer"} (marked as struct parent)
    std::vector<std::string> namespaces;

    DeclContext *DC = D->getDeclContext();
    while (DC) {
        if (auto *ND = dyn_cast<NamespaceDecl>(DC)) {
            if (!ND->isAnonymousNamespace()) {
                // Named namespace: use name directly
                // Mark with prefix to distinguish from struct parents
                namespaces.push_back("ns:" + ND->getName().str());
            } else {
                // Anonymous namespace: generate unique ID
                std::string uniqueId = getAnonymousNamespaceID(ND);
                namespaces.push_back("ns:" + uniqueId);
            }
        } else if (auto *RD = dyn_cast<RecordDecl>(DC)) {
            // Phase 3: Handle nested structs/classes
            // Mark with prefix to distinguish from namespace parents
            namespaces.push_back("rec:" + RD->getName().str());
        }
        DC = DC->getParent();
    }

    // Reverse to get outermost-to-innermost order
    std::reverse(namespaces.begin(), namespaces.end());
    return namespaces;
}

std::string NameMangler::mangleClassName(CXXRecordDecl *RD) {
    // Phase 3: Extract namespace and nested struct hierarchy
    // Supports both namespaces (single _) and nested structs (double __)
    std::vector<std::string> hierarchy = extractNamespaceHierarchy(RD);

    // Build mangled name with proper separators:
    // - Namespace: single underscore (_)
    // - Nested struct: double underscore (__)
    // Example: ns::Outer::Inner → ns_Outer__Inner
    std::string mangledName;
    for (const auto &item : hierarchy) {
        if (item.substr(0, 3) == "ns:") {
            // Namespace: use single underscore
            mangledName += item.substr(3) + "_";
        } else if (item.substr(0, 4) == "rec:") {
            // Nested struct: use double underscore
            mangledName += item.substr(4) + "__";
        }
    }
    mangledName += RD->getName().str();

    return mangledName;
}

std::string NameMangler::mangleMethodName(CXXMethodDecl *MD) {
    // Check if parent is valid (can be null in some edge cases)
    CXXRecordDecl* Parent = MD->getParent();
    if (!Parent) {
        llvm::errs() << "WARNING: CXXMethodDecl has null parent, using method name only: "
                     << MD->getNameAsString() << "\n";
        return MD->getNameAsString();
    }

    // Phase 3: Extract namespace and nested struct hierarchy
    std::vector<std::string> hierarchy = extractNamespaceHierarchy(Parent);

    // Build mangled name with proper separators:
    // - Namespace: single underscore (_)
    // - Nested struct: double underscore (__)
    // - Method: single underscore (_)
    // Example: ns::Outer::Inner::method → ns_Outer__Inner_method
    // Phase 53: Use sanitizeOperatorName() for operators, getNameAsString() for regular methods
    std::string methodName;
    if (MD->isOverloadedOperator()) {
        methodName = sanitizeOperatorName(MD->getOverloadedOperator());
    } else {
        methodName = MD->getNameAsString();
    }

    std::string mangledName;
    for (const auto &item : hierarchy) {
        if (item.substr(0, 3) == "ns:") {
            // Namespace: use single underscore
            mangledName += item.substr(3) + "_";
        } else if (item.substr(0, 4) == "rec:") {
            // Nested struct: use double underscore
            mangledName += item.substr(4) + "__";
        }
    }
    mangledName += Parent->getName().str() + "_" + methodName;

    return mangledName;
}

std::string NameMangler::mangleFunctionName(FunctionDecl *FD) {
    // Prompt #031: extern "C" and Calling Convention Support
    // CRITICAL: Check for extern "C" linkage BEFORE any mangling
    // extern "C" functions must have unmangled names to preserve C ABI
    if (FD->isExternC()) {
        return FD->getName().str();  // Return unmangled name for C linkage
    }

    // Phase 3: Extract namespace hierarchy (no nested structs for standalone functions)
    std::vector<std::string> hierarchy = extractNamespaceHierarchy(FD);

    // Phase 53: Handle operator overloading for standalone functions
    std::string functionName;
    if (FD->isOverloadedOperator()) {
        functionName = sanitizeOperatorName(FD->getOverloadedOperator());
    } else {
        functionName = FD->getName().str();
    }

    // Build mangled name: ns1_ns2_funcName
    // Note: Standalone functions can't be nested in structs, only namespaces
    std::string mangledName;
    for (const auto &item : hierarchy) {
        if (item.substr(0, 3) == "ns:") {
            // Namespace: use single underscore
            mangledName += item.substr(3) + "_";
        }
        // rec: prefix should not appear for standalone functions
    }
    mangledName += functionName;

    return mangledName;
}

// ============================================================================
// Phase 8: Standalone Function Translation (v2.1.0)
// ============================================================================

std::string NameMangler::mangleStandaloneFunction(FunctionDecl *FD) {
    // Phase 2: Registry-backed standalone function mangling
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

    // Phase 53: Handle operator overloading for standalone functions
    std::string functionName;
    if (FD->isOverloadedOperator()) {
        functionName = sanitizeOperatorName(FD->getOverloadedOperator());
    } else {
        functionName = FD->getName().str();
    }

    // Build base name with namespaces
    // NOTE: extractNamespaceHierarchy() returns items with "ns:" or "rec:" prefixes
    std::string baseName;
    for (const auto &item : namespaces) {
        if (item.substr(0, 3) == "ns:") {
            // Namespace: use single underscore, strip "ns:" prefix
            baseName += item.substr(3) + "_";
        }
        // rec: prefix should not appear for standalone functions
    }
    baseName += functionName;

    // Check if already registered (may be called multiple times for same function)
    std::string existing = registry_.getMangledName(baseName, FD);
    if (!existing.empty()) {
        return existing;
    }

    // Determine mangled name based on existing overloads
    std::string mangledName;
    if (!registry_.hasMultipleOverloads(baseName) && registry_.countOverloads(baseName) == 0) {
        // First occurrence - use simple base name
        mangledName = baseName;
    } else {
        // Handle overload: append parameter types
        // Pattern: functionName_paramType1_paramType2_...
        mangledName = baseName;
        for (ParmVarDecl *Param : FD->parameters()) {
            // Skip 'this' parameter - it's implicit in C++ and shouldn't affect overload resolution
            if (Param->getName() == "this") {
                continue;
            }
            mangledName += "_" + getSimpleTypeName(Param->getType());
        }
    }

    // Register with global registry for cross-file tracking
    registry_.registerOverload(baseName, FD, mangledName);

    return mangledName;
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

// ============================================================================
// Phase 53: Operator Name Sanitization
// ============================================================================

std::string NameMangler::sanitizeOperatorName(OverloadedOperatorKind Op) {
    // Convert operator kind to valid C identifier suffix
    // Pattern: operator+ → operator_plus, operator[] → operator_indexer
    switch (Op) {
        // Arithmetic operators
        case OO_Plus:           return "operator_plus";
        case OO_Minus:          return "operator_minus";
        case OO_Star:           return "operator_star";           // Dereference or multiplication
        case OO_Slash:          return "operator_divide";
        case OO_Percent:        return "operator_modulo";

        // Bitwise operators
        case OO_Caret:          return "operator_xor";
        case OO_Amp:            return "operator_amp";            // Address-of or bitwise AND
        case OO_Pipe:           return "operator_pipe";
        case OO_Tilde:          return "operator_tilde";
        case OO_LessLess:       return "operator_left_shift";    // Stream << or bitwise
        case OO_GreaterGreater: return "operator_right_shift";   // Stream >> or bitwise

        // Logical operators
        case OO_Exclaim:        return "operator_not";
        case OO_AmpAmp:         return "operator_and";
        case OO_PipePipe:       return "operator_or";

        // Assignment operators
        case OO_Equal:          return "operator_assign";
        case OO_PlusEqual:      return "operator_plus_assign";
        case OO_MinusEqual:     return "operator_minus_assign";
        case OO_StarEqual:      return "operator_multiply_assign";
        case OO_SlashEqual:     return "operator_divide_assign";
        case OO_PercentEqual:   return "operator_modulo_assign";
        case OO_CaretEqual:     return "operator_xor_assign";
        case OO_AmpEqual:       return "operator_and_assign";
        case OO_PipeEqual:      return "operator_or_assign";
        case OO_LessLessEqual:  return "operator_left_shift_assign";
        case OO_GreaterGreaterEqual: return "operator_right_shift_assign";

        // Comparison operators
        case OO_EqualEqual:     return "operator_equal";
        case OO_ExclaimEqual:   return "operator_not_equal";
        case OO_Less:           return "operator_less";
        case OO_Greater:        return "operator_greater";
        case OO_LessEqual:      return "operator_less_equal";
        case OO_GreaterEqual:   return "operator_greater_equal";
        case OO_Spaceship:      return "operator_spaceship";     // C++20 <=>

        // Increment/Decrement (prefix/postfix handled separately)
        case OO_PlusPlus:       return "operator_increment";
        case OO_MinusMinus:     return "operator_decrement";

        // Special member access operators
        case OO_Arrow:          return "operator_arrow";
        case OO_ArrowStar:      return "operator_arrow_star";    // Rare: ->*
        case OO_Subscript:      return "operator_indexer";       // operator[] - USER PREFERENCE
        case OO_Call:           return "operator_call";

        // Other operators
        case OO_Comma:          return "operator_comma";
        case OO_Conditional:    return "operator_conditional";   // C++23: operator?:
        case OO_Coawait:        return "operator_coawait";       // C++20 coroutines

        // New/Delete (rarely overloaded for custom types)
        case OO_New:            return "operator_new";
        case OO_Delete:         return "operator_delete";
        case OO_Array_New:      return "operator_array_new";
        case OO_Array_Delete:   return "operator_array_delete";

        default:
            return "operator_unknown";
    }
}
