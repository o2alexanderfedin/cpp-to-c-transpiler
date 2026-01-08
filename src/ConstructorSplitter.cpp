/**
 * @file ConstructorSplitter.cpp
 * @brief Implementation of ConstructorSplitter (Story #92)
 */

#include "../include/ConstructorSplitter.h"
#include "../include/VirtualInheritanceAnalyzer.h"
#include "clang/AST/DeclCXX.h"
#include <sstream>

using namespace clang;

ConstructorSplitter::ConstructorSplitter(ASTContext& Context,
                                         const VirtualInheritanceAnalyzer& ViAnalyzer)
    : Context(Context), ViAnalyzer(ViAnalyzer) {}

bool ConstructorSplitter::needsSplitting(const CXXRecordDecl* Record) const {
    if (!Record) {
        return false;
    }

    // Need splitting if class has ANY virtual bases (direct or inherited through hierarchy)
    // Check all bases - if any base is virtual, we need splitting
    for (const auto& base : Record->bases()) {
        if (base.isVirtual()) {
            // Direct virtual base - definitely needs splitting
            return true;
        }

        // Check if non-virtual base has virtual bases in its hierarchy
        const auto* baseRecord = base.getType()->getAsCXXRecordDecl();
        if (baseRecord && needsSplitting(baseRecord)) {
            // Indirect virtual base through this non-virtual base
            return true;
        }
    }

    return false;
}

std::string ConstructorSplitter::generateC1Constructor(const CXXRecordDecl* Record) {
    if (!Record || !needsSplitting(Record)) {
        return "";
    }

    std::ostringstream code;
    std::string className = Record->getNameAsString();
    std::string ctorName = getConstructorName(Record, true);

    // C1 signature: void ClassName_C1(struct ClassName *this, const void **vtt)
    code << "// C1 (Complete Object Constructor) for " << className << "\n";
    code << "void " << ctorName << "(struct " << className << " *this, const void **vtt) {\n";

    // 1. Construct virtual bases first (C1 responsibility)
    std::string vbaseConstruction = generateVirtualBaseConstruction(Record);
    if (!vbaseConstruction.empty()) {
        code << vbaseConstruction;
    }

    // 2. Call base class C2 constructors (not C1!)
    std::string baseCtorCalls = generateBaseConstructorCalls(Record, true);
    if (!baseCtorCalls.empty()) {
        code << baseCtorCalls;
    }

    // 3. Initialize own members
    std::string memberInit = generateMemberInitialization(Record);
    if (!memberInit.empty()) {
        code << memberInit;
    }

    // 4. Set vtable pointers from VTT
    std::string vtableAssign = generateVtableAssignment(Record);
    if (!vtableAssign.empty()) {
        code << vtableAssign;
    }

    code << "}\n";

    return code.str();
}

std::string ConstructorSplitter::generateC2Constructor(const CXXRecordDecl* Record) {
    if (!Record || !needsSplitting(Record)) {
        return "";
    }

    std::ostringstream code;
    std::string className = Record->getNameAsString();
    std::string ctorName = getConstructorName(Record, false);

    // C2 signature: void ClassName_C2(struct ClassName *this, const void **vtt)
    code << "// C2 (Base Object Constructor) for " << className << "\n";
    code << "void " << ctorName << "(struct " << className << " *this, const void **vtt) {\n";

    // C2 does NOT construct virtual bases (that's C1's job)

    // 1. Call base class C2 constructors
    std::string baseCtorCalls = generateBaseConstructorCalls(Record, true);
    if (!baseCtorCalls.empty()) {
        code << baseCtorCalls;
    }

    // 2. Initialize own members
    std::string memberInit = generateMemberInitialization(Record);
    if (!memberInit.empty()) {
        code << memberInit;
    }

    // 3. Set vtable pointers from VTT
    std::string vtableAssign = generateVtableAssignment(Record);
    if (!vtableAssign.empty()) {
        code << vtableAssign;
    }

    code << "}\n";

    return code.str();
}

std::string ConstructorSplitter::generateVirtualBaseConstruction(const CXXRecordDecl* Record) {
    if (!Record) {
        return "";
    }

    std::ostringstream code;
    auto virtualBases = ViAnalyzer.getVirtualBases(Record);

    if (!virtualBases.empty()) {
        code << "    // Construct virtual bases (C1 only)\n";

        for (const auto* vbase : virtualBases) {
            std::string vbaseName = vbase->getNameAsString();

            // Simplified: call C1 constructor for virtual base
            code << "    // TODO: Calculate offset to " << vbaseName << "\n";
            code << "    " << vbaseName << "_C1((struct " << vbaseName << " *)this, vtt);\n";
        }

        code << "\n";
    }

    return code.str();
}

std::string ConstructorSplitter::generateBaseConstructorCalls(const CXXRecordDecl* Record, bool useC2) {
    if (!Record) {
        return "";
    }

    std::ostringstream code;
    bool hasNonVirtualBases = false;

    for (const auto& Base : Record->bases()) {
        if (Base.isVirtual()) {
            continue; // Skip virtual bases (handled separately in C1)
        }

        const Type* baseType = Base.getType().getTypePtr();
        if (!baseType) {
            continue;
        }

        const CXXRecordDecl* baseDecl = baseType->getAsCXXRecordDecl();
        if (!baseDecl) {
            continue;
        }

        if (!hasNonVirtualBases) {
            code << "    // Call base class constructors\n";
            hasNonVirtualBases = true;
        }

        std::string baseName = baseDecl->getNameAsString();
        std::string baseCtor = baseName + (useC2 ? "_C2" : "_C1");

        // Call base constructor with VTT
        code << "    " << baseCtor << "((struct " << baseName << " *)this, vtt);\n";
    }

    if (hasNonVirtualBases) {
        code << "\n";
    }

    return code.str();
}

std::string ConstructorSplitter::generateMemberInitialization(const CXXRecordDecl* Record) {
    if (!Record) {
        return "";
    }

    std::ostringstream code;
    bool hasMembers = false;

    for (const auto* field : Record->fields()) {
        if (!hasMembers) {
            code << "    // Initialize own members\n";
            hasMembers = true;
        }

        std::string fieldName = field->getNameAsString();

        // Simple zero-initialization for now
        code << "    this->" << fieldName << " = 0;\n";
    }

    if (hasMembers) {
        code << "\n";
    }

    return code.str();
}

std::string ConstructorSplitter::generateVtableAssignment(const CXXRecordDecl* Record) {
    if (!Record) {
        return "";
    }

    std::ostringstream code;

    // Set primary vtable pointer from VTT
    code << "    // Set vtable pointer from VTT\n";
    code << "    this->vptr = (const void *)vtt[0];\n";

    return code.str();
}

std::string ConstructorSplitter::getConstructorName(const CXXRecordDecl* Record, bool isC1) const {
    if (!Record) {
        return "";
    }

    std::string className = Record->getNameAsString();
    return className + (isC1 ? "_C1" : "_C2");
}
