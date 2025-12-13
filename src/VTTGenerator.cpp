/**
 * @file VTTGenerator.cpp
 * @brief Implementation of VTTGenerator (Story #91)
 */

#include "../include/VTTGenerator.h"
#include "../include/VirtualInheritanceAnalyzer.h"
#include "clang/AST/DeclCXX.h"
#include <sstream>

using namespace clang;

VTTGenerator::VTTGenerator(ASTContext& Context, const VirtualInheritanceAnalyzer& ViAnalyzer)
    : Context(Context), ViAnalyzer(ViAnalyzer) {}

std::string VTTGenerator::generateVTT(const CXXRecordDecl* Record) {
    if (!Record) {
        return "";
    }

    // Only generate VTT for classes with virtual bases
    if (!ViAnalyzer.hasVirtualBases(Record)) {
        return "";
    }

    std::ostringstream code;
    std::string className = Record->getNameAsString();
    std::string vttName = getVTTName(Record);

    // Collect VTT entries
    std::vector<std::string> entries;
    collectVTTEntries(Record, entries);

    if (entries.empty()) {
        return "";
    }

    // Generate VTT array
    code << "// VTT (Virtual Table Table) for " << className << "\n";
    code << "const void* " << vttName << "[] = {\n";

    for (size_t i = 0; i < entries.size(); ++i) {
        code << "    " << entries[i];
        if (i < entries.size() - 1) {
            code << ",";
        }
        code << "\n";
    }

    code << "};\n";

    return code.str();
}

size_t VTTGenerator::getVTTEntryCount(const CXXRecordDecl* Record) {
    if (!Record || !ViAnalyzer.hasVirtualBases(Record)) {
        return 0;
    }

    std::vector<std::string> entries;
    collectVTTEntries(Record, entries);
    return entries.size();
}

std::vector<std::string> VTTGenerator::getVTTEntries(const CXXRecordDecl* Record) {
    std::vector<std::string> entries;
    if (Record && ViAnalyzer.hasVirtualBases(Record)) {
        collectVTTEntries(Record, entries);
    }
    return entries;
}

std::string VTTGenerator::getVTTName(const CXXRecordDecl* Record) const {
    if (!Record) {
        return "";
    }
    return "__vtt_" + Record->getNameAsString();
}

void VTTGenerator::collectVTTEntries(const CXXRecordDecl* Record,
                                     std::vector<std::string>& entries) {
    if (!Record) {
        return;
    }

    // Itanium ABI VTT ordering:
    // 1. Primary virtual pointer
    addPrimaryVtableEntry(Record, entries);

    // 2. Secondary VTTs (for non-virtual proper base classes)
    // 3. Secondary virtual pointers (construction vtables)
    addBaseConstructorEntries(Record, entries);

    // 4. Virtual VTTs (for virtual base classes)
    addVirtualBaseEntries(Record, entries);
}

void VTTGenerator::addPrimaryVtableEntry(const CXXRecordDecl* Record,
                                         std::vector<std::string>& entries) {
    if (!Record) {
        return;
    }

    // First entry: primary vtable for complete object
    std::string vtableRef = getVtableReference(Record, "_primary");
    entries.push_back(vtableRef + "  // Primary vtable");
}

void VTTGenerator::addBaseConstructorEntries(const CXXRecordDecl* Record,
                                             std::vector<std::string>& entries) {
    if (!Record) {
        return;
    }

    // Add construction vtable entries for each non-virtual base that has virtual bases
    for (const auto& Base : Record->bases()) {
        if (Base.isVirtual()) {
            continue; // Skip virtual bases (handled separately)
        }

        const Type* baseType = Base.getType().getTypePtr();
        if (!baseType) {
            continue;
        }

        const CXXRecordDecl* baseDecl = baseType->getAsCXXRecordDecl();
        if (!baseDecl) {
            continue;
        }

        // If base has virtual bases, it needs a construction vtable entry
        if (ViAnalyzer.hasVirtualBases(baseDecl)) {
            std::string baseName = baseDecl->getNameAsString();
            std::string vtableRef = getVtableReference(Record, "_" + baseName + "_base");
            entries.push_back(vtableRef + "  // " + baseName + " base constructor vtable");
        }
    }
}

void VTTGenerator::addVirtualBaseEntries(const CXXRecordDecl* Record,
                                         std::vector<std::string>& entries) {
    if (!Record) {
        return;
    }

    // Add entries for each virtual base
    auto virtualBases = ViAnalyzer.getVirtualBases(Record);
    for (const auto* vbase : virtualBases) {
        std::string vbaseName = vbase->getNameAsString();
        std::string vtableRef = getVtableReference(Record, "_" + vbaseName);
        entries.push_back(vtableRef + "  // " + vbaseName + " virtual base vtable");
    }
}

std::string VTTGenerator::getVtableReference(const CXXRecordDecl* Record,
                                              const std::string& suffix) const {
    if (!Record) {
        return "";
    }

    std::string className = Record->getNameAsString();
    return "&__vtable_" + className + suffix;
}
