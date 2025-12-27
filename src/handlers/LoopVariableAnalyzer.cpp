/**
 * @file LoopVariableAnalyzer.cpp
 * @brief Implementation of LoopVariableAnalyzer
 *
 * TDD Implementation: Start with simple by-value variables, expand to references.
 */

#include "handlers/LoopVariableAnalyzer.h"
#include "clang/AST/Type.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

LoopVariableInfo LoopVariableAnalyzer::analyze(const clang::CXXForRangeStmt* RFS) {
    LoopVariableInfo info;

    if (!RFS) {
        return info;
    }

    // Extract loop variable declaration
    const clang::VarDecl* VD = getLoopVariable(RFS);
    if (!VD) {
        return info;
    }

    info.varDecl = VD;
    info.name = VD->getNameAsString();
    info.type = VD->getType();

    // Determine if auto type
    info.isAuto = isAutoType(info.type);

    // Determine const qualification
    info.isConst = info.type.isConstQualified();

    // Determine if reference
    info.isReference = info.type->isReferenceType();

    // Determine value category
    info.category = determineValueCategory(info.type);

    // Check for structured binding
    info.isStructuredBinding = isStructuredBinding(VD);
    if (info.isStructuredBinding) {
        info.bindingNames = extractBindingNames(VD);
    }

    return info;
}

const clang::VarDecl* LoopVariableAnalyzer::getLoopVariable(const clang::CXXForRangeStmt* RFS) {
    if (!RFS) return nullptr;
    return RFS->getLoopVariable();
}

ValueCategory LoopVariableAnalyzer::determineValueCategory(clang::QualType type) {
    // Check if it's a reference type
    if (type->isLValueReferenceType()) {
        // Check if const-qualified
        clang::QualType pointeeType = type->getPointeeType();
        if (pointeeType.isConstQualified()) {
            return ValueCategory::ByConstRef;
        } else {
            return ValueCategory::ByMutableRef;
        }
    } else if (type->isRValueReferenceType()) {
        // auto&& (universal reference) - deferred to Phase 57
        return ValueCategory::ByRValueRef;
    } else {
        // By-value
        return ValueCategory::ByValue;
    }
}

bool LoopVariableAnalyzer::isAutoType(clang::QualType type) {
    // Remove references to check the underlying type
    clang::QualType underlyingType = type;
    if (type->isReferenceType()) {
        underlyingType = type->getPointeeType();
    }

    // Check if it's an AutoType
    return underlyingType->getContainedAutoType() != nullptr;
}

bool LoopVariableAnalyzer::isStructuredBinding(const clang::VarDecl* VD) {
    if (!VD) return false;

    // Check if it's a DecompositionDecl (C++17 structured bindings)
    return llvm::isa<clang::DecompositionDecl>(VD);
}

std::vector<std::string> LoopVariableAnalyzer::extractBindingNames(const clang::VarDecl* VD) {
    std::vector<std::string> names;

    if (!VD) return names;

    // Check if it's a DecompositionDecl
    if (const auto* DD = llvm::dyn_cast<clang::DecompositionDecl>(VD)) {
        for (const auto* binding : DD->bindings()) {
            names.push_back(binding->getNameAsString());
        }
    }

    return names;
}

} // namespace cpptoc
