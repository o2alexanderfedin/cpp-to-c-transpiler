/**
 * @file VtableGenerator.cpp
 * @brief Implementation of VtableGenerator
 */

#include "../include/VtableGenerator.h"
#include "../include/OverrideResolver.h"
#include "../include/VirtualInheritanceAnalyzer.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/RecordLayout.h"
#include <sstream>
#include <map>
#include <functional>
#include <cstddef>

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

    // Story #84: Add type_info pointer as first field (Itanium ABI vtable[-1])
    // In C, we place it at offset 0 instead of -1
    code << "    const struct __class_type_info *type_info;  /**< RTTI type_info pointer (Itanium ABI vtable[-1]) */\n";

    // Get methods in vtable order
    auto methods = getVtableMethodOrder(Record);

    // Generate function pointers for each method
    for (auto* method : methods) {
        code << "    " << generateFunctionPointer(method, className) << ";\n";
    }

    code << "};\n";

    return code.str();
}

// ============================================================================
// Phase 31-02: COM-Style Static Declarations for Virtual Methods
// ============================================================================

std::string VtableGenerator::generateStaticDeclarations(const CXXRecordDecl* Record) {
    if (!Record || !Analyzer.isPolymorphic(Record)) {
        return ""; // Not polymorphic, no declarations needed
    }

    std::ostringstream decls;
    std::string className = Record->getNameAsString();
    auto methods = getVtableMethodOrder(Record);

    // Add comment header
    decls << "// Static declarations for " << className << " virtual methods\n";

    // Generate declaration for each virtual method
    for (auto* method : methods) {
        decls << getMethodSignature(method, className) << ";\n";
    }

    return decls.str();
}

std::string VtableGenerator::getMethodSignature(const CXXMethodDecl* Method,
                                                 const std::string& ClassName) {
    std::ostringstream sig;

    // static keyword
    sig << "static ";

    // Return type
    QualType returnType = Method->getReturnType();
    sig << getTypeString(returnType) << " ";

    // Function name (use name mangling for C function name)
    if (isa<CXXDestructorDecl>(Method)) {
        // Destructor: use __dtor suffix to match vtable field naming
        sig << ClassName << "__dtor";
    } else {
        // Regular method: ClassName_methodName
        sig << ClassName << "_" << Method->getNameAsString();
        // TODO: Handle overloaded methods with parameter-based mangling if needed
    }

    // Parameters: always starts with 'this' pointer
    sig << "(struct " << ClassName << " *this";

    // Add method parameters
    for (unsigned i = 0; i < Method->getNumParams(); ++i) {
        const ParmVarDecl* param = Method->getParamDecl(i);
        sig << ", ";
        sig << getTypeString(param->getType());

        // Add parameter name if available
        if (!param->getName().empty()) {
            sig << " " << param->getNameAsString();
        } else {
            sig << " arg" << i;
        }
    }

    sig << ")";

    return sig.str();
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

// ============================================================================
// Story #90: Virtual Base Offset Table Generation
// ============================================================================

std::string VtableGenerator::generateVtableWithVirtualBaseOffsets(
    const CXXRecordDecl* Record,
    const VirtualInheritanceAnalyzer& ViAnalyzer) {

    if (!Record || !Analyzer.isPolymorphic(Record)) {
        return ""; // Not polymorphic, no vtable needed
    }

    std::ostringstream code;
    std::string className = Record->getNameAsString();

    // Generate vtable struct
    code << "struct " << className << "_vtable {\n";

    // Add type_info pointer (Itanium ABI vtable[-1])
    code << "    const struct __class_type_info *type_info;  /**< RTTI type_info pointer (Itanium ABI vtable[-1]) */\n";

    // Story #90: Add virtual base offset table (negative offset area in Itanium ABI)
    // In our C representation, we put it before function pointers
    auto virtualBases = ViAnalyzer.getVirtualBases(Record);
    if (!virtualBases.empty()) {
        code << "\n    // Virtual base offset table (Itanium ABI negative offset area)\n";

        for (const auto* vbase : virtualBases) {
            std::string vbaseName = vbase->getNameAsString();
            code << "    ptrdiff_t vbase_offset_to_" << vbaseName << ";  /**< Offset to virtual base " << vbaseName << " */\n";
        }
        code << "\n";
    }

    // Get methods in vtable order
    auto methods = getVtableMethodOrder(Record);

    // Generate function pointers for each method
    for (auto* method : methods) {
        code << "    " << generateFunctionPointer(method, className) << ";\n";
    }

    code << "};\n";

    return code.str();
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

    std::ostringstream code;
    std::string derivedName = Derived->getNameAsString();
    std::string vbaseName = VirtualBase->getNameAsString();

    // Generate helper function to access virtual base
    code << "// Helper function to access virtual base " << vbaseName << " from " << derivedName << "\n";
    code << "static inline struct " << vbaseName << "* " << derivedName << "_get_" << vbaseName << "_base(";
    code << "struct " << derivedName << " *obj) {\n";
    code << "    // Get vbase_offset from vtable\n";
    code << "    struct " << derivedName << "_vtable *vtable = (struct " << derivedName << "_vtable *)obj->vptr;\n";
    code << "    ptrdiff_t offset = vtable->vbase_offset_to_" << vbaseName << ";\n";
    code << "    \n";
    code << "    // Calculate virtual base pointer\n";
    code << "    return (struct " << vbaseName << " *)((char*)obj + offset);\n";
    code << "}\n";

    return code.str();
}
