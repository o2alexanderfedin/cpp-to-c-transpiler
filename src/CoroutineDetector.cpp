/**
 * @file CoroutineDetector.cpp
 * @brief Implementation of CoroutineDetector (Story #102)
 */

#include "../include/CoroutineDetector.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtCXX.h"
#include <sstream>

using namespace clang;

namespace {

/**
 * @brief Visitor to detect coroutine keywords and count suspend points
 */
class CoroutineVisitor : public RecursiveASTVisitor<CoroutineVisitor> {
public:
    bool hasCoroutineKeyword = false;
    size_t suspendCount = 0;

    bool VisitCoroutineBodyStmt(CoroutineBodyStmt* S) {
        hasCoroutineKeyword = true;
        return true;
    }

    bool VisitCoawaitExpr(CoawaitExpr* E) {
        hasCoroutineKeyword = true;
        suspendCount++;
        return true;
    }

    bool VisitCoyieldExpr(CoyieldExpr* E) {
        hasCoroutineKeyword = true;
        suspendCount++;
        return true;
    }

    bool VisitCoreturnStmt(CoreturnStmt* S) {
        hasCoroutineKeyword = true;
        suspendCount++;
        return true;
    }
};

} // anonymous namespace

CoroutineDetector::CoroutineDetector(ASTContext& Context)
    : Context(Context) {}

bool CoroutineDetector::isCoroutine(const FunctionDecl* FD) const {
    if (!FD || !FD->hasBody()) {
        return false;
    }

    CoroutineVisitor visitor;
    visitor.TraverseStmt(FD->getBody());

    return visitor.hasCoroutineKeyword;
}

std::string CoroutineDetector::generateFrameStructure(const FunctionDecl* FD) {
    if (!FD || !isCoroutine(FD)) {
        return "";
    }

    std::ostringstream code;
    std::string frameName = getFrameName(FD);
    std::string funcName = FD->getNameAsString();

    code << "// Coroutine frame structure for " << funcName << "\n";
    code << "struct " << frameName << " {\n";

    // 1. State field for suspend points
    code << "    int state;                    // Current suspend point (0, 1, 2, ...)\n";

    // 2. Resume function pointer
    code << "    void (*resume_fn)(void*);     // Resume function pointer\n";

    // 3. Destroy function pointer
    code << "    void (*destroy_fn)(void*);    // Destroy function pointer\n";

    // 4. Promise object (simplified - using void* for now)
    code << "    void* promise;                // Promise object\n";

    // 5. Parameter fields
    std::string paramFields = generateParameterFields(FD);
    if (!paramFields.empty()) {
        code << paramFields;
    }

    code << "};\n";

    // Generate state enum
    size_t suspendPointCount = countSuspendPoints(FD);
    if (suspendPointCount > 0) {
        code << "\n";
        code << generateStateEnum(FD, suspendPointCount);
    }

    return code.str();
}

size_t CoroutineDetector::countSuspendPoints(const FunctionDecl* FD) const {
    if (!FD || !FD->hasBody()) {
        return 0;
    }

    CoroutineVisitor visitor;
    visitor.TraverseStmt(FD->getBody());

    return visitor.suspendCount;
}

std::string CoroutineDetector::getFrameName(const FunctionDecl* FD) const {
    if (!FD) {
        return "";
    }

    return FD->getNameAsString() + "_frame";
}

std::string CoroutineDetector::generateStateEnum(const FunctionDecl* FD, size_t suspendCount) {
    if (!FD || suspendCount == 0) {
        return "";
    }

    std::ostringstream code;
    std::string funcName = FD->getNameAsString();

    code << "// State enum for " << funcName << " suspend points\n";
    code << "enum " << funcName << "_state {\n";
    code << "    " << funcName << "_STATE_INITIAL = 0,\n";

    for (size_t i = 1; i <= suspendCount; ++i) {
        code << "    " << funcName << "_STATE_SUSPEND_" << i;
        if (i < suspendCount) {
            code << ",";
        }
        code << "\n";
    }

    code << "};\n";

    return code.str();
}

std::string CoroutineDetector::generateParameterFields(const FunctionDecl* FD) {
    if (!FD) {
        return "";
    }

    std::ostringstream code;
    bool hasParams = false;

    for (const auto* param : FD->parameters()) {
        if (!hasParams) {
            code << "    // Coroutine parameters\n";
            hasParams = true;
        }

        std::string paramType = getTypeString(param->getType());
        std::string paramName = param->getNameAsString();

        if (paramName.empty()) {
            paramName = "param_" + std::to_string(param->getFunctionScopeIndex());
        }

        code << "    " << paramType << " " << paramName << ";\n";
    }

    return code.str();
}

std::string CoroutineDetector::getTypeString(QualType Type) {
    // Get the canonical type and remove qualifiers for base type
    QualType CanonicalType = Type.getCanonicalType();

    // Handle basic types
    if (CanonicalType->isIntegerType()) {
        if (CanonicalType->isSignedIntegerType()) {
            return "int";
        } else {
            return "unsigned int";
        }
    }

    if (CanonicalType->isFloatingType()) {
        if (CanonicalType->isSpecificBuiltinType(BuiltinType::Float)) {
            return "float";
        } else if (CanonicalType->isSpecificBuiltinType(BuiltinType::Double)) {
            return "double";
        }
    }

    if (CanonicalType->isPointerType()) {
        QualType PointeeType = CanonicalType->getPointeeType();
        return getTypeString(PointeeType) + "*";
    }

    if (CanonicalType->isReferenceType()) {
        QualType RefType = CanonicalType.getNonReferenceType();
        return getTypeString(RefType) + "*";  // Convert references to pointers in C
    }

    // For record types (structs/classes), use struct name
    if (const RecordType* RT = CanonicalType->getAs<RecordType>()) {
        if (const RecordDecl* RD = RT->getDecl()) {
            return "struct " + RD->getNameAsString();
        }
    }

    // Fallback to printing the type
    return Type.getAsString();
}
