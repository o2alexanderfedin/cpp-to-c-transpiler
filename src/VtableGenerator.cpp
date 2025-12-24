/**
 * @file VtableGenerator.cpp
 * @brief Implementation of VtableGenerator
 *
 * Phase 31-04: Optimized for performance with:
 * - Pre-allocated string buffers (reserve())
 * - Direct string concatenation (faster than ostringstream)
 * - Cached method properties (avoid repeated AST queries)
 * - No legacy code paths (single, clean code path)
 */

#include "../include/VtableGenerator.h"
#include "../include/MethodSignatureHelper.h"
#include "../include/OverrideResolver.h"
#include "../include/VirtualInheritanceAnalyzer.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/RecordLayout.h"
#include <string>
#include <cstddef>

using namespace clang;

VtableGenerator::VtableGenerator(ASTContext& Context, VirtualMethodAnalyzer& Analyzer,
                                  OverrideResolver* Resolver)
    : Context(Context), Analyzer(Analyzer), Resolver(Resolver) {}

std::string VtableGenerator::generateVtableStruct(const CXXRecordDecl* Record) {
    if (!Record || !Analyzer.isPolymorphic(Record)) {
        return ""; // Not polymorphic, no vtable needed
    }

    // Phase 31-04: Pre-allocate string buffer for better performance
    std::string code;
    code.reserve(512);  // Typical vtable struct ~300-500 chars

    std::string className = Record->getNameAsString();

    // Generate vtable struct
    code += "struct ";
    code += className;
    code += "_vtable {\n";

    // Story #84: Add type_info pointer as first field (Itanium ABI vtable[-1])
    // In C, we place it at offset 0 instead of -1
    code += "    const struct __class_type_info *type_info;  /**< RTTI type_info pointer (Itanium ABI vtable[-1]) */\n";

    // Get methods in vtable order
    auto methods = getVtableMethodOrder(Record);

    // Generate function pointers for each method
    for (auto* method : methods) {
        code += "    ";
        code += generateFunctionPointer(method, className);
        code += ";\n";
    }

    code += "};\n";

    return code;
}

// ============================================================================
// Phase 31-02: COM-Style Static Declarations for Virtual Methods
// ============================================================================

std::string VtableGenerator::generateStaticDeclarations(const CXXRecordDecl* Record) {
    if (!Record || !Analyzer.isPolymorphic(Record)) {
        return ""; // Not polymorphic, no declarations needed
    }

    // Phase 31-04: Pre-allocate string buffer for better performance
    std::string decls;
    std::string className = Record->getNameAsString();
    auto methods = getVtableMethodOrder(Record);

    // Estimate size: ~120 chars per declaration
    decls.reserve(50 + methods.size() * 120);

    // Add comment header
    decls += "// Static declarations for ";
    decls += className;
    decls += " virtual methods\n";

    // Generate declaration for each virtual method
    for (auto* method : methods) {
        decls += getMethodSignature(method, className);
        decls += ";\n";
    }

    return decls;
}

std::string VtableGenerator::getMethodSignature(const CXXMethodDecl* Method,
                                                 const std::string& ClassName) {
    // Phase 31-03: Delegate to MethodSignatureHelper (DRY principle)
    return MethodSignatureHelper::generateSignature(Method, ClassName);
}

std::vector<CXXMethodDecl*> VtableGenerator::getVtableMethodOrder(const CXXRecordDecl* Record) {
    if (!Record) {
        return {};
    }

    // Phase 31-04: OverrideResolver is always provided (required dependency)
    // Legacy fallback code removed - all callers now provide OverrideResolver
    return Resolver->resolveVtableLayout(Record);
}

std::string VtableGenerator::generateFunctionPointer(const CXXMethodDecl* Method,
                                                      const std::string& ClassName) {
    // Phase 31-04: Pre-allocate and use string concatenation for better performance
    std::string ptr;
    ptr.reserve(100);  // Typical function pointer ~60-100 chars

    // Cache method properties
    const bool isDestructor = isa<CXXDestructorDecl>(Method);
    const unsigned numParams = Method->getNumParams();

    // Return type
    QualType returnType = Method->getReturnType();
    ptr += getTypeString(returnType);
    ptr += " ";

    // Function pointer name
    if (isDestructor) {
        ptr += "(*destructor)";
    } else {
        ptr += "(*";
        ptr += Method->getNameAsString();
        ptr += ")";
    }

    // Parameters: always starts with 'this' pointer
    ptr += "(struct ";
    ptr += ClassName;
    ptr += " *this";

    // Add method parameters
    for (unsigned i = 0; i < numParams; ++i) {
        const ParmVarDecl* param = Method->getParamDecl(i);
        ptr += ", ";
        ptr += getTypeString(param->getType());

        // Add parameter name if available
        if (!param->getName().empty()) {
            ptr += " ";
            ptr += param->getNameAsString();
        } else {
            ptr += " arg";
            ptr += std::to_string(i);
        }
    }

    ptr += ")";

    return ptr;
}

std::string VtableGenerator::getTypeString(QualType Type) {
    // Phase 31-03: Delegate to MethodSignatureHelper (DRY principle)
    return MethodSignatureHelper::getTypeString(Type);
}

// ============================================================================
// Story #90: Virtual Base Offset Table Generation
// ============================================================================

std::string VtableGenerator::generateVtableWithVirtualBaseOffsets(
    const CXXRecordDecl* Record,
    const VirtualInheritanceAnalyzer& ViAnalyzer) {

    if (!Record || !Analyzer.isPolymorphic(Record)) {
        return ""; // Not polymorphic, no vtable needed
    }

    // Phase 31-04: Pre-allocate string buffer
    std::string code;
    code.reserve(512);

    std::string className = Record->getNameAsString();

    // Generate vtable struct
    code += "struct ";
    code += className;
    code += "_vtable {\n";

    // Add type_info pointer (Itanium ABI vtable[-1])
    code += "    const struct __class_type_info *type_info;  /**< RTTI type_info pointer (Itanium ABI vtable[-1]) */\n";

    // Story #90: Add virtual base offset table (negative offset area in Itanium ABI)
    // In our C representation, we put it before function pointers
    auto virtualBases = ViAnalyzer.getVirtualBases(Record);
    if (!virtualBases.empty()) {
        code += "\n    // Virtual base offset table (Itanium ABI negative offset area)\n";

        for (const auto* vbase : virtualBases) {
            std::string vbaseName = vbase->getNameAsString();
            code += "    ptrdiff_t vbase_offset_to_";
            code += vbaseName;
            code += ";  /**< Offset to virtual base ";
            code += vbaseName;
            code += " */\n";
        }
        code += "\n";
    }

    // Get methods in vtable order
    auto methods = getVtableMethodOrder(Record);

    // Generate function pointers for each method
    for (auto* method : methods) {
        code += "    ";
        code += generateFunctionPointer(method, className);
        code += ";\n";
    }

    code += "};\n";

    return code;
}

ptrdiff_t VtableGenerator::calculateVirtualBaseOffset(
    const CXXRecordDecl* Derived,
    const CXXRecordDecl* VirtualBase,
    ASTContext& Context) {

    if (!Derived || !VirtualBase) {
        return 0;
    }

    // Use Clang's RecordLayout to get accurate offset information
    const ASTRecordLayout& DerivedLayout = Context.getASTRecordLayout(Derived);

    // Virtual bases come after all non-virtual members in the Itanium ABI
    // They are stored at the end of the object layout

    // Try to get the virtual base offset from Clang's layout
    // Note: This is a simplified implementation
    // In a complete implementation, we would traverse the inheritance graph

    // For now, calculate based on the size of non-virtual part
    CharUnits offset = DerivedLayout.getNonVirtualSize();

    // If there are multiple virtual bases, we need to account for their layout
    // This is a simplified calculation - in reality, each virtual base has its own offset

    return offset.getQuantity();
}

std::string VtableGenerator::generateVirtualBaseAccessHelper(
    const CXXRecordDecl* Derived,
    const CXXRecordDecl* VirtualBase) {

    if (!Derived || !VirtualBase) {
        return "";
    }

    // Phase 31-04: Pre-allocate string buffer
    std::string code;
    code.reserve(300);

    std::string derivedName = Derived->getNameAsString();
    std::string vbaseName = VirtualBase->getNameAsString();

    // Generate helper function to access virtual base
    code += "// Helper function to access virtual base ";
    code += vbaseName;
    code += " from ";
    code += derivedName;
    code += "\n";
    code += "static inline struct ";
    code += vbaseName;
    code += "* ";
    code += derivedName;
    code += "_get_";
    code += vbaseName;
    code += "_base(";
    code += "struct ";
    code += derivedName;
    code += " *obj) {\n";
    code += "    // Get vbase_offset from vtable\n";
    code += "    struct ";
    code += derivedName;
    code += "_vtable *vtable = (struct ";
    code += derivedName;
    code += "_vtable *)obj->vptr;\n";
    code += "    ptrdiff_t offset = vtable->vbase_offset_to_";
    code += vbaseName;
    code += ";\n";
    code += "    \n";
    code += "    // Calculate virtual base pointer\n";
    code += "    return (struct ";
    code += vbaseName;
    code += " *)((char*)obj + offset);\n";
    code += "}\n";

    return code;
}
