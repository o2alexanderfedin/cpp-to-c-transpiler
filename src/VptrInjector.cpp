/**
 * @file VptrInjector.cpp
 * @brief Implementation of Story #169: Vptr Field Injection
 */

#include "VptrInjector.h"
#include "CNodeBuilder.h"

using namespace clang;

VptrInjector::VptrInjector(ASTContext& Context, VirtualMethodAnalyzer& Analyzer)
    : Context(Context), Analyzer(Analyzer) {}

bool VptrInjector::injectVptrField(const CXXRecordDecl* Record,
                                    std::vector<FieldDecl*>& fields) {
    // Only inject vptr if class is polymorphic
    if (!Analyzer.isPolymorphic(Record)) {
        return false;
    }

    // Create vptr field
    FieldDecl* vptrField = createVptrField(Record);

    // Insert vptr as FIRST field (offset 0) - critical for ABI compatibility
    fields.insert(fields.begin(), vptrField);

    return true;
}

const std::string& VptrInjector::getVptrFieldName() {
    static const std::string name = "vptr";
    return name;
}

std::string VptrInjector::getVtableTypeName(const std::string& ClassName) {
    return ClassName + "_vtable";
}

FieldDecl* VptrInjector::createVptrField(const CXXRecordDecl* Record) {
    QualType vptrType = buildVptrType(Record);

    CNodeBuilder Builder(Context);
    return Builder.fieldDecl(vptrType, getVptrFieldName());
}

QualType VptrInjector::buildVptrType(const CXXRecordDecl* Record) {
    // Build type: const struct {ClassName}_vtable*

    std::string className = Record->getNameAsString();
    std::string vtableTypeName = getVtableTypeName(className);

    CNodeBuilder Builder(Context);

    // Create incomplete struct type for vtable (forward declaration)
    // We don't need the full definition here, just the pointer type
    QualType vtableStructType = Builder.structType(vtableTypeName);

    // Make it const: const struct {ClassName}_vtable
    QualType constVtableType = Context.getConstType(vtableStructType);

    // Make it a pointer: const struct {ClassName}_vtable*
    QualType vptrType = Context.getPointerType(constVtableType);

    return vptrType;
}
