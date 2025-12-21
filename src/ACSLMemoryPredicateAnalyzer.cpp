// Phase 6: Advanced Memory Predicates (v1.23.0)
// Epic #193: ACSL Annotation Generation for Transpiled Code
//
// Implementation following SOLID and TDD principles

#include "ACSLMemoryPredicateAnalyzer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <sstream>
#include <algorithm>

using namespace clang;

// Constructors
ACSLMemoryPredicateAnalyzer::ACSLMemoryPredicateAnalyzer()
    : ACSLGenerator() {
}

ACSLMemoryPredicateAnalyzer::ACSLMemoryPredicateAnalyzer(ACSLLevel level)
    : ACSLGenerator(level) {
}

ACSLMemoryPredicateAnalyzer::ACSLMemoryPredicateAnalyzer(ACSLLevel level, ACSLOutputMode mode)
    : ACSLGenerator(level, mode) {
}

// Main predicate generation method
std::string ACSLMemoryPredicateAnalyzer::generateMemoryPredicates(const FunctionDecl* func) {
    if (!func) return "";

    std::vector<std::string> requires;
    std::vector<std::string> ensures;

    // Check what type of memory function this is
    bool isAlloc = isAllocationFunction(func);
    bool isDealloc = isDeallocationFunction(func);
    bool isRealloc = isReallocationFunction(func);
    bool hasArithmetic = hasPointerArithmetic(func);
    bool hasBaseAddr = computesBaseAddress(func);

    // If not a memory-related function, return empty
    if (!isAlloc && !isDealloc && !isRealloc && !hasArithmetic && !hasBaseAddr) {
        return "";
    }

    // Generate appropriate predicates
    if (isAlloc || isRealloc) {
        std::string allocable = generateAllocablePrecondition(func);
        if (!allocable.empty()) {
            requires.push_back(allocable);
        }

        std::string fresh = generateFreshPostcondition(func);
        if (!fresh.empty()) {
            ensures.push_back(fresh);
        }

        std::string blockLength = generateBlockLengthPostcondition(func);
        if (!blockLength.empty()) {
            ensures.push_back(blockLength);
        }

        // For allocation functions returning pointers, ensure \valid(\result) or \result == \null
        if (func->getReturnType()->isPointerType()) {
            ensures.push_back("\\valid(\\result) || \\result == \\null");
        }

        // Add preconditions for non-size pointer parameters (like struct pointers)
        for (unsigned i = 0; i < func->getNumParams(); ++i) {
            const ParmVarDecl* param = func->getParamDecl(i);
            if (param->getType()->isPointerType()) {
                // Skip if this is the size parameter or if it's void**
                const ParmVarDecl* sizeParam = detectSizeParameter(func);
                if (param != sizeParam) {
                    QualType pointeeType = param->getType()->getPointeeType();
                    if (!pointeeType->isPointerType() && !pointeeType->isVoidType()) {
                        // This is a non-void, non-pointer-to-pointer parameter (like Data*)
                        std::ostringstream oss;
                        oss << "\\valid(" << param->getNameAsString() << ")";
                        requires.push_back(oss.str());
                    }
                }
            }
        }
    }

    if (isDealloc || isRealloc) {
        std::string freeable = generateFreeablePrecondition(func);
        if (!freeable.empty()) {
            requires.push_back(freeable);
        }

        if (isDealloc) {
            std::string invalidAfterFree = generateInvalidAfterFreePostcondition(func);
            if (!invalidAfterFree.empty()) {
                ensures.push_back(invalidAfterFree);
            }
        }
    }

    if (hasArithmetic) {
        std::string arithmeticSafety = generatePointerArithmeticSafety(func);
        if (!arithmeticSafety.empty()) {
            requires.push_back(arithmeticSafety);
        }

        // Ensure result is valid after arithmetic
        ensures.push_back("\\valid(\\result)");
    }

    if (hasBaseAddr) {
        std::string baseAddr = generateBaseAddrPostcondition(func);
        if (!baseAddr.empty()) {
            ensures.push_back(baseAddr);
        }
    }

    // Build contract string
    std::ostringstream oss;

    for (const auto& req : requires) {
        oss << "  requires " << req << ";\n";
    }

    for (const auto& ens : ensures) {
        oss << "  ensures " << ens << ";\n";
    }

    std::string contract = oss.str();
    if (contract.empty()) {
        return "";
    }

    return formatACSLComment(contract);
}

// Check if function is an allocation function
bool ACSLMemoryPredicateAnalyzer::isAllocationFunction(const FunctionDecl* func) const {
    if (!func) return false;

    std::string funcName = func->getNameAsString();

    // Check function name
    if (isAllocationName(funcName)) {
        return true;
    }

    // Check function body for allocation calls
    if (bodyContainsAllocation(func)) {
        return true;
    }

    return false;
}

// Check if function is a deallocation function
bool ACSLMemoryPredicateAnalyzer::isDeallocationFunction(const FunctionDecl* func) const {
    if (!func) return false;

    std::string funcName = func->getNameAsString();

    // Check function name
    if (isDeallocationName(funcName)) {
        return true;
    }

    // Check function body for deallocation calls
    if (bodyContainsDeallocation(func)) {
        return true;
    }

    return false;
}

// Check if function is a reallocation function
bool ACSLMemoryPredicateAnalyzer::isReallocationFunction(const FunctionDecl* func) const {
    if (!func) return false;

    std::string funcName = func->getNameAsString();

    // Check function name
    if (isReallocationName(funcName)) {
        return true;
    }

    // Check function body for reallocation calls
    if (bodyContainsReallocation(func)) {
        return true;
    }

    return false;
}

// Check if function has pointer arithmetic
bool ACSLMemoryPredicateAnalyzer::hasPointerArithmetic(const FunctionDecl* func) const {
    if (!func) return false;

    std::string funcName = func->getNameAsString();

    // Check if name suggests offset/pointer arithmetic
    if (isOffsetName(funcName)) {
        return true;
    }

    // Check if return type is pointer and has offset parameter
    if (func->getReturnType()->isPointerType()) {
        const ParmVarDecl* offsetParam = detectOffsetParameter(func);
        if (offsetParam) {
            return true;
        }
    }

    return false;
}

// Check if function computes base address
bool ACSLMemoryPredicateAnalyzer::computesBaseAddress(const FunctionDecl* func) const {
    if (!func) return false;

    std::string funcName = func->getNameAsString();

    return isBaseAddrName(funcName);
}

// Generate allocable precondition
std::string ACSLMemoryPredicateAnalyzer::generateAllocablePrecondition(const FunctionDecl* func) {
    if (!func) return "";

    const ParmVarDecl* sizeParam = detectSizeParameter(func);
    if (!sizeParam) {
        return "\\allocable(size)";
    }

    std::ostringstream oss;
    oss << "\\allocable(" << sizeParam->getNameAsString() << ")";
    return oss.str();
}

// Generate freeable precondition
std::string ACSLMemoryPredicateAnalyzer::generateFreeablePrecondition(const FunctionDecl* func) {
    if (!func) return "";

    const ParmVarDecl* ptrParam = detectPointerParameter(func);
    if (!ptrParam) {
        return "\\freeable(ptr)";
    }

    std::ostringstream oss;
    oss << "\\freeable(" << ptrParam->getNameAsString() << ")";
    return oss.str();
}

// Generate block_length postcondition
std::string ACSLMemoryPredicateAnalyzer::generateBlockLengthPostcondition(const FunctionDecl* func) {
    if (!func) return "";

    const ParmVarDecl* sizeParam = detectSizeParameter(func);
    if (!sizeParam) {
        return "";
    }

    std::ostringstream oss;
    oss << "\\block_length(\\result) == " << sizeParam->getNameAsString();
    return oss.str();
}

// Generate base_addr postcondition
std::string ACSLMemoryPredicateAnalyzer::generateBaseAddrPostcondition(const FunctionDecl* func) {
    if (!func) return "";

    const ParmVarDecl* ptrParam = detectPointerParameter(func);
    if (!ptrParam) {
        return "\\result == \\base_addr(ptr)";
    }

    std::ostringstream oss;
    oss << "\\result == \\base_addr(" << ptrParam->getNameAsString() << ")";
    return oss.str();
}

// Generate fresh memory postcondition
std::string ACSLMemoryPredicateAnalyzer::generateFreshPostcondition(const FunctionDecl* func) {
    if (!func) return "";

    const ParmVarDecl* sizeParam = detectSizeParameter(func);
    if (!sizeParam) {
        return "\\fresh(\\result, size)";
    }

    std::ostringstream oss;
    oss << "\\fresh(\\result, " << sizeParam->getNameAsString() << ")";
    return oss.str();
}

// Generate invalid after free postcondition
std::string ACSLMemoryPredicateAnalyzer::generateInvalidAfterFreePostcondition(const FunctionDecl* func) {
    if (!func) return "";

    const ParmVarDecl* ptrParam = detectPointerParameter(func);
    if (!ptrParam) {
        return "!\\valid(ptr)";
    }

    // Handle double-pointer case (void** ptr)
    QualType type = ptrParam->getType();
    if (type->isPointerType()) {
        QualType pointeeType = type->getPointeeType();
        if (pointeeType->isPointerType()) {
            // For safe_free(void** ptr), we ensure *ptr is not valid
            std::ostringstream oss;
            oss << "!\\valid(*" << ptrParam->getNameAsString() << ")";
            return oss.str();
        }
    }

    std::ostringstream oss;
    oss << "!\\valid(" << ptrParam->getNameAsString() << ")";
    return oss.str();
}

// Generate pointer arithmetic safety precondition
std::string ACSLMemoryPredicateAnalyzer::generatePointerArithmeticSafety(const FunctionDecl* func) {
    if (!func) return "";

    const ParmVarDecl* ptrParam = detectPointerParameter(func);
    const ParmVarDecl* offsetParam = detectOffsetParameter(func);

    if (!ptrParam || !offsetParam) {
        return "";
    }

    std::ostringstream oss;
    oss << offsetParam->getNameAsString() << " < \\block_length("
        << ptrParam->getNameAsString() << ")";
    return oss.str();
}

// Detect size parameter
const ParmVarDecl* ACSLMemoryPredicateAnalyzer::detectSizeParameter(const FunctionDecl* func) const {
    if (!func) return nullptr;

    // For reallocation functions, prefer "new_size" over "old_size"
    if (isReallocationFunction(func)) {
        for (unsigned i = 0; i < func->getNumParams(); ++i) {
            const ParmVarDecl* param = func->getParamDecl(i);
            std::string paramName = param->getNameAsString();
            std::string lowerParamName = paramName;
            std::transform(lowerParamName.begin(), lowerParamName.end(),
                          lowerParamName.begin(), ::tolower);

            // Prefer parameters with "new" in the name (e.g., new_size)
            if (lowerParamName.find("new") != std::string::npos &&
                lowerParamName.find("size") != std::string::npos) {
                return param;
            }
        }
    }

    // Look for common size parameter names
    // Including patterns like "new_size", "old_size", etc.
    std::vector<std::string> sizeNames = {"size", "n", "count", "length", "len", "num"};
    return findParameterByPattern(func, sizeNames);
}

// Detect pointer parameter
const ParmVarDecl* ACSLMemoryPredicateAnalyzer::detectPointerParameter(const FunctionDecl* func) const {
    if (!func) return nullptr;

    // Find first pointer parameter
    for (unsigned i = 0; i < func->getNumParams(); ++i) {
        const ParmVarDecl* param = func->getParamDecl(i);
        if (param->getType()->isPointerType()) {
            return param;
        }
    }

    return nullptr;
}

// Detect offset parameter
const ParmVarDecl* ACSLMemoryPredicateAnalyzer::detectOffsetParameter(const FunctionDecl* func) const {
    if (!func) return nullptr;

    // Look for common offset parameter names
    std::vector<std::string> offsetNames = {"offset", "off", "delta", "distance", "index", "idx"};
    return findParameterByPattern(func, offsetNames);
}

// Check if function name suggests allocation
bool ACSLMemoryPredicateAnalyzer::isAllocationName(const std::string& funcName) const {
    std::string lowerName = funcName;
    std::transform(lowerName.begin(), lowerName.end(), lowerName.begin(), ::tolower);

    return lowerName.find("alloc") != std::string::npos ||
           lowerName.find("create") != std::string::npos ||
           lowerName.find("new") != std::string::npos ||
           lowerName.find("make") != std::string::npos ||
           lowerName == "malloc" ||
           lowerName == "calloc";
}

// Check if function name suggests deallocation
bool ACSLMemoryPredicateAnalyzer::isDeallocationName(const std::string& funcName) const {
    std::string lowerName = funcName;
    std::transform(lowerName.begin(), lowerName.end(), lowerName.begin(), ::tolower);

    return lowerName.find("free") != std::string::npos ||
           lowerName.find("delete") != std::string::npos ||
           lowerName.find("release") != std::string::npos ||
           lowerName.find("destroy") != std::string::npos ||
           lowerName.find("deallocate") != std::string::npos;
}

// Check if function name suggests reallocation
bool ACSLMemoryPredicateAnalyzer::isReallocationName(const std::string& funcName) const {
    std::string lowerName = funcName;
    std::transform(lowerName.begin(), lowerName.end(), lowerName.begin(), ::tolower);

    return lowerName.find("realloc") != std::string::npos ||
           lowerName.find("resize") != std::string::npos ||
           lowerName.find("expand") != std::string::npos;
}

// Check if function name suggests offset
bool ACSLMemoryPredicateAnalyzer::isOffsetName(const std::string& funcName) const {
    std::string lowerName = funcName;
    std::transform(lowerName.begin(), lowerName.end(), lowerName.begin(), ::tolower);

    return lowerName.find("offset") != std::string::npos ||
           lowerName.find("advance") != std::string::npos ||
           lowerName.find("next") != std::string::npos ||
           lowerName.find("prev") != std::string::npos;
}

// Check if function name suggests base address
bool ACSLMemoryPredicateAnalyzer::isBaseAddrName(const std::string& funcName) const {
    std::string lowerName = funcName;
    std::transform(lowerName.begin(), lowerName.end(), lowerName.begin(), ::tolower);

    return lowerName.find("base") != std::string::npos ||
           lowerName.find("align") != std::string::npos ||
           lowerName.find("round") != std::string::npos;
}

// Analyze function body for allocation calls
bool ACSLMemoryPredicateAnalyzer::bodyContainsAllocation(const FunctionDecl* func) const {
    if (!func || !func->hasBody()) return false;

    // TODO: Implement RecursiveASTVisitor to search for malloc/new calls
    // For now, simple heuristic based on return type
    return func->getReturnType()->isPointerType();
}

// Analyze function body for deallocation calls
bool ACSLMemoryPredicateAnalyzer::bodyContainsDeallocation(const FunctionDecl* func) const {
    if (!func || !func->hasBody()) return false;

    // TODO: Implement RecursiveASTVisitor to search for free/delete calls
    return false;
}

// Analyze function body for reallocation calls
bool ACSLMemoryPredicateAnalyzer::bodyContainsReallocation(const FunctionDecl* func) const {
    if (!func || !func->hasBody()) return false;

    // TODO: Implement RecursiveASTVisitor to search for realloc calls
    return false;
}

// Find parameter by name pattern
const ParmVarDecl* ACSLMemoryPredicateAnalyzer::findParameterByPattern(
    const FunctionDecl* func,
    const std::vector<std::string>& namePattern) const {

    if (!func) return nullptr;

    for (unsigned i = 0; i < func->getNumParams(); ++i) {
        const ParmVarDecl* param = func->getParamDecl(i);
        std::string paramName = param->getNameAsString();
        std::string lowerParamName = paramName;
        std::transform(lowerParamName.begin(), lowerParamName.end(),
                      lowerParamName.begin(), ::tolower);

        for (const auto& pattern : namePattern) {
            std::string lowerPattern = pattern;
            std::transform(lowerPattern.begin(), lowerPattern.end(),
                          lowerPattern.begin(), ::tolower);

            if (lowerParamName == lowerPattern ||
                lowerParamName.find(lowerPattern) != std::string::npos) {
                return param;
            }
        }
    }

    return nullptr;
}
