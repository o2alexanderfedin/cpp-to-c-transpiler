/**
 * @file RangeTypeAnalyzer.cpp
 * @brief Implementation of RangeTypeAnalyzer
 *
 * TDD Implementation: Start with C array detection, expand to containers.
 */

#include "handlers/RangeTypeAnalyzer.h"
#include "clang/AST/Type.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

RangeClassification RangeTypeAnalyzer::analyze(const clang::CXXForRangeStmt* RFS) {
    if (!RFS) {
        return RangeClassification{};
    }

    // Extract range expression
    const clang::Expr* rangeExpr = getRangeExpr(RFS);
    if (!rangeExpr) {
        return RangeClassification{};
    }

    // Classify the range type
    return classifyRangeType(rangeExpr);
}

bool RangeTypeAnalyzer::isRangeForStmt(const clang::Stmt* S) {
    return S && llvm::isa<clang::CXXForRangeStmt>(S);
}

const clang::Expr* RangeTypeAnalyzer::getRangeExpr(const clang::CXXForRangeStmt* RFS) {
    if (!RFS) return nullptr;
    return RFS->getRangeInit();
}

RangeClassification RangeTypeAnalyzer::classifyRangeType(const clang::Expr* rangeExpr) {
    if (!rangeExpr) {
        return RangeClassification{};
    }

    RangeClassification result;

    // Get the type of the range expression
    clang::QualType rangeType = rangeExpr->getType();

    // Check for const qualification
    result.isConst = rangeType.isConstQualified();

    // Remove qualifiers for classification
    rangeType = rangeType.getUnqualifiedType();

    // Try C array first
    auto arraySize = tryGetCArraySize(rangeType);
    if (arraySize.has_value()) {
        result.rangeType = RangeType::CArray;
        result.arraySize = arraySize;
        result.beginEndKind = BeginEndKind::NotApplicable;
        result.elementType = extractElementType(rangeType);
        result.typeName = "array";
        return result;
    }

    // Try STL container
    std::string containerName = tryGetSTLContainerName(rangeType);
    if (!containerName.empty()) {
        result.rangeType = RangeType::STLContainer;
        result.typeName = containerName;
        result.beginEndKind = determineBeginEndKind(rangeType);
        result.elementType = extractElementType(rangeType);
        return result;
    }

    // Check for custom type with begin/end
    BeginEndKind kind = determineBeginEndKind(rangeType);
    if (kind != BeginEndKind::Unknown) {
        result.rangeType = RangeType::CustomType;
        result.beginEndKind = kind;
        result.elementType = extractElementType(rangeType);
        result.typeName = rangeType.getAsString();
        return result;
    }

    // Unknown/unsupported range type
    return RangeClassification{};
}

std::optional<uint64_t> RangeTypeAnalyzer::tryGetCArraySize(clang::QualType type) {
    // Check if it's a constant array type
    if (const auto* CAT = llvm::dyn_cast<clang::ConstantArrayType>(type.getTypePtr())) {
        // Get the size as uint64_t
        return CAT->getSize().getZExtValue();
    }

    return std::nullopt;
}

std::string RangeTypeAnalyzer::tryGetSTLContainerName(clang::QualType type) {
    // Get the canonical type
    type = type.getCanonicalType();

    // Check if it's a class/struct type
    if (const auto* RT = llvm::dyn_cast<clang::RecordType>(type.getTypePtr())) {
        const auto* RD = RT->getDecl();
        if (!RD) return "";

        // Check if it's a template specialization (STL containers are templates)
        if (const auto* CTSD = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(RD)) {
            std::string name = CTSD->getName().str();

            // Check for common STL containers
            if (name == "vector" || name == "basic_string" ||
                name == "array" || name == "deque" ||
                name == "list" || name == "forward_list" ||
                name == "set" || name == "multiset" ||
                name == "map" || name == "multimap" ||
                name == "unordered_set" || name == "unordered_multiset" ||
                name == "unordered_map" || name == "unordered_multimap") {
                return name;
            }
        }
    }

    return "";
}

BeginEndKind RangeTypeAnalyzer::determineBeginEndKind(clang::QualType type) {
    // Get the record type
    const auto* RT = type->getAs<clang::RecordType>();
    if (!RT) return BeginEndKind::Unknown;

    const auto* RD = RT->getDecl();
    if (!RD) return BeginEndKind::Unknown;

    // Check for begin() and end() member functions
    const auto* CXXRecord = llvm::dyn_cast<clang::CXXRecordDecl>(RD);
    if (!CXXRecord) return BeginEndKind::Unknown;

    bool hasBegin = false;
    bool hasEnd = false;

    for (const auto* method : CXXRecord->methods()) {
        if (method->getName() == "begin") hasBegin = true;
        if (method->getName() == "end") hasEnd = true;
    }

    if (hasBegin && hasEnd) {
        return BeginEndKind::MemberFunction;
    }

    // TODO: Check for free functions begin()/end() in Phase 54 extensions
    // For now, if we don't find member functions, assume Unknown
    return BeginEndKind::Unknown;
}

clang::QualType RangeTypeAnalyzer::extractElementType(clang::QualType type) {
    // For C arrays, get the element type
    if (const auto* AT = llvm::dyn_cast<clang::ArrayType>(type.getTypePtr())) {
        return AT->getElementType();
    }

    // For class templates (STL containers), extract first template argument
    if (const auto* RT = llvm::dyn_cast<clang::RecordType>(type.getTypePtr())) {
        if (const auto* CTSD = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(RT->getDecl())) {
            const auto& args = CTSD->getTemplateArgs();
            if (args.size() > 0 && args[0].getKind() == clang::TemplateArgument::Type) {
                return args[0].getAsType();
            }
        }
    }

    // Fallback: return the type itself
    return type;
}

} // namespace cpptoc
