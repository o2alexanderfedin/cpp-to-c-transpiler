/**
 * @file CoroutineDetector.cpp
 * @brief Implementation of CoroutineDetector (Story #102)
 */

#include "../include/CoroutineDetector.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtCXX.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Analysis/CFG.h"
#include <sstream>
#include <set>
#include <map>

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

    // 4. Promise object (extract actual promise type)
    std::string promiseTypeName = extractPromiseTypeName(FD);
    code << "    " << promiseTypeName << " promise;";
    code << "                // Promise object\n";

    // 5. Parameter fields
    std::string paramFields = generateParameterFields(FD);
    if (!paramFields.empty()) {
        code << paramFields;
    }

    // 6. Local variable fields (NEW: Story #102 - Local Variable Analysis)
    std::vector<LocalVariableInfo> localVars = analyzeLocalVariables(FD);
    std::string localVarFields = generateLocalVariableFields(localVars);
    if (!localVarFields.empty()) {
        code << localVarFields;
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

std::vector<LocalVariableInfo> CoroutineDetector::analyzeLocalVariables(const FunctionDecl* FD) {
    std::vector<LocalVariableInfo> result;

    if (!FD || !FD->hasBody() || !isCoroutine(FD)) {
        return result;
    }

    // Step 1: Find all suspend points in the function
    class SuspendPointCollector : public RecursiveASTVisitor<SuspendPointCollector> {
    public:
        std::vector<const Stmt*> suspendPoints;

        bool VisitCoawaitExpr(CoawaitExpr* E) {
            suspendPoints.push_back(E);
            return true;
        }

        bool VisitCoyieldExpr(CoyieldExpr* E) {
            suspendPoints.push_back(E);
            return true;
        }

        bool VisitCoreturnStmt(CoreturnStmt* S) {
            suspendPoints.push_back(S);
            return true;
        }
    };

    SuspendPointCollector suspendCollector;
    suspendCollector.TraverseStmt(FD->getBody());

    if (suspendCollector.suspendPoints.empty()) {
        return result;  // No suspend points, no locals need to be promoted
    }

    // Step 2: Find all local variables
    class LocalVarCollector : public RecursiveASTVisitor<LocalVarCollector> {
    public:
        std::vector<const VarDecl*> localVars;

        bool VisitVarDecl(VarDecl* VD) {
            if (VD->isLocalVarDecl() && !VD->isStaticLocal()) {
                localVars.push_back(VD);
            }
            return true;
        }
    };

    LocalVarCollector varCollector;
    varCollector.TraverseStmt(FD->getBody());

    // Step 3: For each local variable, check if it's used after a suspend point
    class VariableUseFinder : public RecursiveASTVisitor<VariableUseFinder> {
    public:
        const VarDecl* targetVar;
        std::set<const Stmt*> useLocations;

        explicit VariableUseFinder(const VarDecl* var) : targetVar(var) {}

        bool VisitDeclRefExpr(DeclRefExpr* DRE) {
            if (DRE->getDecl() == targetVar) {
                useLocations.insert(DRE);
            }
            return true;
        }
    };

    // Build a simple ordering map based on source locations
    auto getStmtOrder = [&](const Stmt* S) -> unsigned {
        if (!S) return 0;
        return Context.getSourceManager().getFileOffset(S->getBeginLoc());
    };

    auto getDeclOrder = [&](const Decl* D) -> unsigned {
        if (!D) return 0;
        return Context.getSourceManager().getFileOffset(D->getBeginLoc());
    };

    for (const VarDecl* var : varCollector.localVars) {
        unsigned varDeclOrder = getDeclOrder(var);

        // Find all uses of this variable
        VariableUseFinder useFinder(var);
        useFinder.TraverseStmt(FD->getBody());

        // Check if variable is used after any suspend point
        bool spansSupsend = false;

        for (const Stmt* suspendPoint : suspendCollector.suspendPoints) {
            unsigned suspendOrder = getStmtOrder(suspendPoint);

            // Variable must be declared before the suspend point
            if (varDeclOrder >= suspendOrder) {
                continue;
            }

            // Check if variable is used after this suspend point
            for (const Stmt* use : useFinder.useLocations) {
                unsigned useOrder = getStmtOrder(use);
                if (useOrder > suspendOrder) {
                    spansSupsend = true;
                    break;
                }
            }

            if (spansSupsend) {
                break;
            }
        }

        // Also check if variable is declared before a suspend and the variable
        // is part of a loop condition that includes suspend points
        if (!spansSupsend) {
            for (const Stmt* suspendPoint : suspendCollector.suspendPoints) {
                unsigned suspendOrder = getStmtOrder(suspendPoint);

                // If variable declared before suspend, it might span
                if (varDeclOrder < suspendOrder) {
                    // Check if any use exists (even before suspend in loop contexts)
                    if (!useFinder.useLocations.empty()) {
                        spansSupsend = true;
                        break;
                    }
                }
            }
        }

        if (spansSupsend) {
            std::string varName = var->getNameAsString();
            std::string varType = getTypeString(var->getType());
            result.emplace_back(varName, varType, var);
        }
    }

    return result;
}

std::string CoroutineDetector::generateLocalVariableFields(const std::vector<LocalVariableInfo>& localVars) {
    if (localVars.empty()) {
        return "";
    }

    std::ostringstream code;
    code << "    // Local variables spanning suspend points\n";

    for (const auto& var : localVars) {
        code << "    " << var.type << " " << var.name << ";\n";
    }

    return code.str();
}

std::string CoroutineDetector::extractPromiseTypeName(const FunctionDecl* FD) {
    if (!FD || !isCoroutine(FD)) {
        return "void*";
    }

    // Get the return type
    QualType returnType = FD->getReturnType();
    if (returnType.isNull()) {
        return "void*";
    }

    // Get the class/record declaration
    const RecordType* RT = returnType->getAs<RecordType>();
    if (!RT) {
        // Try to get through desugaring
        QualType canonicalType = returnType.getCanonicalType();
        RT = canonicalType->getAs<RecordType>();
        if (!RT) {
            return "void*";
        }
    }

    const CXXRecordDecl* returnClass = dyn_cast<CXXRecordDecl>(RT->getDecl());
    if (!returnClass) {
        return "void*";
    }

    // Check if the class has a nested promise_type
    bool hasPromiseType = false;
    for (auto *D : returnClass->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "promise_type" && RD->isCompleteDefinition()) {
                hasPromiseType = true;
                break;
            }
        }
        // Also check type aliases
        if (auto *TD = dyn_cast<TypedefNameDecl>(D)) {
            if (TD->getNameAsString() == "promise_type") {
                hasPromiseType = true;
                break;
            }
        }
    }

    if (!hasPromiseType) {
        return "void*";
    }

    // Generate the C struct name
    return "struct " + getPromiseStructName(returnClass);
}

std::string CoroutineDetector::getPromiseStructName(const CXXRecordDecl* returnType) {
    if (!returnType) {
        return "";
    }

    std::ostringstream structName;

    // Get the base class name
    std::string baseName = returnType->getNameAsString();
    structName << baseName;

    // Handle template specializations
    if (const auto* CTSD = dyn_cast<ClassTemplateSpecializationDecl>(returnType)) {
        const auto& templateArgs = CTSD->getTemplateArgs();

        for (unsigned i = 0; i < templateArgs.size(); ++i) {
            const auto& arg = templateArgs[i];

            if (arg.getKind() == clang::TemplateArgument::Type) {
                QualType argType = arg.getAsType();
                std::string argTypeName;

                // Handle basic types
                if (argType->isIntegerType()) {
                    if (argType->isSignedIntegerType()) {
                        argTypeName = "int";
                    } else {
                        argTypeName = "unsigned_int";
                    }
                } else if (argType->isFloatingType()) {
                    if (argType->isSpecificBuiltinType(BuiltinType::Float)) {
                        argTypeName = "float";
                    } else if (argType->isSpecificBuiltinType(BuiltinType::Double)) {
                        argTypeName = "double";
                    } else {
                        argTypeName = argType.getAsString();
                    }
                } else if (const RecordType* RT = argType->getAs<RecordType>()) {
                    if (const RecordDecl* RD = RT->getDecl()) {
                        argTypeName = RD->getNameAsString();
                    } else {
                        argTypeName = argType.getAsString();
                    }
                } else {
                    argTypeName = argType.getAsString();
                }

                // Replace spaces and special characters with underscores
                for (char& c : argTypeName) {
                    if (c == ' ' || c == ':' || c == '<' || c == '>') {
                        c = '_';
                    }
                }

                structName << "_" << argTypeName;
            } else if (arg.getKind() == clang::TemplateArgument::Integral) {
                // Handle integer template arguments
                llvm::SmallString<32> intStr;
                arg.getAsIntegral().toString(intStr, 10);
                structName << "_" << intStr.c_str();
            }
        }
    }

    structName << "_promise";
    return structName.str();
}
