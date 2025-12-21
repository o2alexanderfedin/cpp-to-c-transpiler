// Phase 1 (v1.18.0): ACSL Statement Annotations Implementation
// Plan: .planning/phases/01-statement-annotations/PLAN.md
//
// Implementation following SOLID and TDD principles

#include "ACSLStatementAnnotator.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Type.h"
#include <sstream>
#include <algorithm>

using namespace clang;

// ============================================================================
// Constructors
// ============================================================================

ACSLStatementAnnotator::ACSLStatementAnnotator()
    : ACSLGenerator() {
}

ACSLStatementAnnotator::ACSLStatementAnnotator(ACSLLevel level)
    : ACSLGenerator(level) {
}

ACSLStatementAnnotator::ACSLStatementAnnotator(ACSLLevel level, ACSLOutputMode mode)
    : ACSLGenerator(level, mode) {
}

// ============================================================================
// Main annotation method
// ============================================================================

std::string ACSLStatementAnnotator::annotateFunction(const FunctionDecl *func,
                                                      AnnotationLevel level) {
    if (!func || level == AnnotationLevel::None) {
        return "";
    }

    if (!func->hasBody()) {
        return "";
    }

    // Use visitor to collect annotations
    StatementVisitor visitor(this, level);
    visitor.TraverseStmt(func->getBody());

    // Build annotated function body
    std::ostringstream oss;
    const auto& annotations = visitor.getAnnotations();

    // For now, just collect and return the annotations as a formatted string
    // In full integration, we would interleave these with the actual code
    for (const auto& pair : annotations) {
        oss << pair.second << "\n";
    }

    return oss.str();
}

// ============================================================================
// StatementVisitor implementation
// ============================================================================

bool ACSLStatementAnnotator::StatementVisitor::VisitStmt(Stmt* stmt) {
    if (!stmt || !m_annotator->needsAnnotation(stmt, m_level)) {
        return true; // Continue traversal
    }

    // Extract safety property and generate annotation
    std::string safetyProperty = m_annotator->extractSafetyProperty(stmt);
    if (!safetyProperty.empty()) {
        m_annotations.push_back(std::make_pair(stmt, safetyProperty));
    }

    // Check for specific statement patterns
    if (const Expr* expr = m_annotator->getStatementExpression(stmt)) {
        // Pointer dereference
        if (const Expr* ptrExpr = m_annotator->detectPointerDereference(expr)) {
            std::string assertion = m_annotator->generateAssert(ptrExpr);
            if (!assertion.empty()) {
                m_annotations.push_back(std::make_pair(stmt, assertion));
            }
        }

        // Array access
        if (const ArraySubscriptExpr* arrayExpr = m_annotator->detectArrayAccess(expr)) {
            std::string assertion = m_annotator->generateAssert(arrayExpr);
            if (!assertion.empty()) {
                m_annotations.push_back(std::make_pair(stmt, assertion));
            }
        }

        // Division operation
        if (const BinaryOperator* divOp = m_annotator->detectDivisionOperation(expr)) {
            std::string assertion = m_annotator->generateAssert(divOp->getRHS());
            if (!assertion.empty()) {
                m_annotations.push_back(std::make_pair(stmt, assertion));
            }
        }

        // Cast operation (Full level only)
        if (m_level == AnnotationLevel::Full) {
            if (const CastExpr* castExpr = m_annotator->detectCastOperation(expr)) {
                std::string assertion = m_annotator->generateAssert(castExpr);
                if (!assertion.empty()) {
                    m_annotations.push_back(std::make_pair(stmt, assertion));
                }
            }
        }
    }

    // Buffer operations (Full level only)
    if (m_level == AnnotationLevel::Full && m_annotator->detectBufferOperation(stmt)) {
        std::string bufferCheck = m_annotator->extractBufferConstraint(stmt);
        if (!bufferCheck.empty()) {
            m_annotations.push_back(std::make_pair(stmt, "//@ assert " + bufferCheck + ";"));
        }
    }

    return true; // Continue traversal
}

// ============================================================================
// Annotation generation methods
// ============================================================================

std::string ACSLStatementAnnotator::generateAssert(const Expr *expr) {
    if (!expr) return "";

    std::ostringstream oss;
    oss << "//@ assert ";

    // Determine assertion type based on expression
    if (const UnaryOperator* unaryOp = dyn_cast<UnaryOperator>(expr)) {
        if (unaryOp->getOpcode() == UO_Deref) {
            // Pointer dereference
            const Expr* ptrExpr = unaryOp->getSubExpr()->IgnoreImpCasts();
            oss << extractPointerValidity(ptrExpr);
        }
    } else if (const ArraySubscriptExpr* arrayExpr = dyn_cast<ArraySubscriptExpr>(expr)) {
        // Array access
        oss << extractArrayBounds(arrayExpr);
    } else if (const BinaryOperator* binOp = dyn_cast<BinaryOperator>(expr)) {
        if (binOp->getOpcode() == BO_Div || binOp->getOpcode() == BO_Rem) {
            // Division or modulo
            oss << extractNonZeroConstraint(binOp->getRHS());
        }
    } else if (const CastExpr* castExpr = dyn_cast<CastExpr>(expr)) {
        // Cast operation
        oss << extractCastConstraint(castExpr);
    } else if (const DeclRefExpr* declRef = dyn_cast<DeclRefExpr>(expr)) {
        // Variable reference - might be a pointer
        QualType type = declRef->getType();
        if (type->isPointerType()) {
            oss << extractPointerValidity(expr);
        }
    } else {
        // Generic expression - try to extract validity
        QualType type = expr->getType();
        if (type->isPointerType()) {
            oss << extractPointerValidity(expr);
        } else {
            return ""; // No assertion needed
        }
    }

    oss << ";";
    return oss.str();
}

std::string ACSLStatementAnnotator::generateAssume(const Expr *expr) {
    if (!expr) return "";

    std::ostringstream oss;
    oss << "//@ assume ";

    // Assume annotations are used for validated contexts
    // For now, return empty - will be expanded in future iterations

    return "";
}

std::string ACSLStatementAnnotator::generateCheck(const Expr *expr) {
    if (!expr) return "";

    std::ostringstream oss;
    oss << "//@ check ";

    // Check annotations are for proof obligations only
    // For now, return empty - will be expanded in future iterations

    return "";
}

// ============================================================================
// Statement analysis methods
// ============================================================================

bool ACSLStatementAnnotator::needsAnnotation(const Stmt *stmt, AnnotationLevel level) {
    if (!stmt || level == AnnotationLevel::None) {
        return false;
    }

    // Check if statement contains operations that need annotation
    if (const Expr* expr = getStatementExpression(stmt)) {
        // Pointer dereference
        if (detectPointerDereference(expr)) {
            return true;
        }

        // Array access
        if (detectArrayAccess(expr)) {
            return true;
        }

        // Division operation
        if (detectDivisionOperation(expr)) {
            return true;
        }

        // Cast operation (Full level only)
        if (level == AnnotationLevel::Full && detectCastOperation(expr)) {
            return true;
        }
    }

    // Buffer operations (Full level only)
    if (level == AnnotationLevel::Full && detectBufferOperation(stmt)) {
        return true;
    }

    return false;
}

std::string ACSLStatementAnnotator::extractSafetyProperty(const Stmt *stmt) {
    if (!stmt) return "";

    const Expr* expr = getStatementExpression(stmt);
    if (!expr) return "";

    // Try to extract safety property from expression
    std::ostringstream oss;

    // Check for pointer dereference
    if (const Expr* ptrExpr = detectPointerDereference(expr)) {
        oss << "//@ assert " << extractPointerValidity(ptrExpr) << ";";
        return oss.str();
    }

    // Check for array access
    if (const ArraySubscriptExpr* arrayExpr = detectArrayAccess(expr)) {
        oss << "//@ assert " << extractArrayBounds(arrayExpr) << ";";
        return oss.str();
    }

    // Check for division
    if (const BinaryOperator* divOp = detectDivisionOperation(expr)) {
        oss << "//@ assert " << extractNonZeroConstraint(divOp->getRHS()) << ";";
        return oss.str();
    }

    return "";
}

// ============================================================================
// Detection methods
// ============================================================================

const Expr* ACSLStatementAnnotator::detectPointerDereference(const Expr *expr) {
    if (!expr) return nullptr;

    expr = expr->IgnoreImpCasts();

    // Unary dereference operator
    if (const UnaryOperator* unaryOp = dyn_cast<UnaryOperator>(expr)) {
        if (unaryOp->getOpcode() == UO_Deref) {
            return unaryOp->getSubExpr()->IgnoreImpCasts();
        }
    }

    // Member access through pointer
    if (const MemberExpr* memberExpr = dyn_cast<MemberExpr>(expr)) {
        if (memberExpr->isArrow()) {
            return memberExpr->getBase()->IgnoreImpCasts();
        }
    }

    // Array subscript (also a pointer dereference)
    if (const ArraySubscriptExpr* arrayExpr = dyn_cast<ArraySubscriptExpr>(expr)) {
        return arrayExpr->getBase()->IgnoreImpCasts();
    }

    // Recursively check sub-expressions
    for (const Stmt* child : expr->children()) {
        if (const Expr* childExpr = dyn_cast_or_null<Expr>(child)) {
            if (const Expr* result = detectPointerDereference(childExpr)) {
                return result;
            }
        }
    }

    return nullptr;
}

const ArraySubscriptExpr* ACSLStatementAnnotator::detectArrayAccess(const Expr *expr) {
    if (!expr) return nullptr;

    expr = expr->IgnoreImpCasts();

    // Direct array subscript
    if (const ArraySubscriptExpr* arrayExpr = dyn_cast<ArraySubscriptExpr>(expr)) {
        return arrayExpr;
    }

    // Recursively check sub-expressions
    for (const Stmt* child : expr->children()) {
        if (const Expr* childExpr = dyn_cast_or_null<Expr>(child)) {
            if (const ArraySubscriptExpr* result = detectArrayAccess(childExpr)) {
                return result;
            }
        }
    }

    return nullptr;
}

const BinaryOperator* ACSLStatementAnnotator::detectDivisionOperation(const Expr *expr) {
    if (!expr) return nullptr;

    expr = expr->IgnoreImpCasts();

    // Binary division or modulo operator
    if (const BinaryOperator* binOp = dyn_cast<BinaryOperator>(expr)) {
        if (binOp->getOpcode() == BO_Div || binOp->getOpcode() == BO_Rem) {
            return binOp;
        }
    }

    // Recursively check sub-expressions
    for (const Stmt* child : expr->children()) {
        if (const Expr* childExpr = dyn_cast_or_null<Expr>(child)) {
            if (const BinaryOperator* result = detectDivisionOperation(childExpr)) {
                return result;
            }
        }
    }

    return nullptr;
}

const CastExpr* ACSLStatementAnnotator::detectCastOperation(const Expr *expr) {
    if (!expr) return nullptr;

    expr = expr->IgnoreImpCasts();

    // Dynamic cast (C++)
    if (const CXXDynamicCastExpr* dynCast = dyn_cast<CXXDynamicCastExpr>(expr)) {
        return dynCast;
    }

    // Static cast (C++)
    if (const CXXStaticCastExpr* staticCast = dyn_cast<CXXStaticCastExpr>(expr)) {
        return staticCast;
    }

    // Reinterpret cast (C++)
    if (const CXXReinterpretCastExpr* reinterpretCast = dyn_cast<CXXReinterpretCastExpr>(expr)) {
        return reinterpretCast;
    }

    // C-style cast
    if (const CStyleCastExpr* cCast = dyn_cast<CStyleCastExpr>(expr)) {
        return cCast;
    }

    return nullptr;
}

bool ACSLStatementAnnotator::detectBufferOperation(const Stmt *stmt) {
    if (!stmt) return false;

    // Look for function calls like strcpy, strcat, memcpy, etc.
    if (const CallExpr* callExpr = dyn_cast<CallExpr>(stmt)) {
        if (const FunctionDecl* func = callExpr->getDirectCallee()) {
            std::string funcName = func->getNameAsString();

            // List of buffer-related functions
            static const std::vector<std::string> bufferFuncs = {
                "strcpy", "strcat", "strncpy", "strncat",
                "memcpy", "memmove", "memset",
                "sprintf", "snprintf", "gets", "scanf"
            };

            return std::find(bufferFuncs.begin(), bufferFuncs.end(), funcName) != bufferFuncs.end();
        }
    }

    // Recursively check children
    for (const Stmt* child : stmt->children()) {
        if (detectBufferOperation(child)) {
            return true;
        }
    }

    return false;
}

// ============================================================================
// Extraction methods
// ============================================================================

std::string ACSLStatementAnnotator::extractPointerValidity(const Expr *ptrExpr) {
    if (!ptrExpr) return "";

    std::ostringstream oss;

    // Get pointer name or expression
    std::string ptrName;
    if (const DeclRefExpr* declRef = dyn_cast<DeclRefExpr>(ptrExpr->IgnoreImpCasts())) {
        ptrName = declRef->getNameInfo().getAsString();
    } else if (const MemberExpr* memberExpr = dyn_cast<MemberExpr>(ptrExpr->IgnoreImpCasts())) {
        ptrName = memberExpr->getMemberNameInfo().getAsString();
    } else {
        ptrName = "ptr"; // Generic name
    }

    // Check if it's a const pointer (use \valid_read)
    QualType type = ptrExpr->getType();
    if (type->isPointerType()) {
        QualType pointeeType = type->getPointeeType();
        if (pointeeType.isConstQualified()) {
            oss << "\\valid_read(" << ptrName << ")";
        } else {
            oss << "\\valid(" << ptrName << ")";
        }
    } else {
        oss << "\\valid(" << ptrName << ")";
    }

    return oss.str();
}

std::string ACSLStatementAnnotator::extractArrayBounds(const ArraySubscriptExpr *arrayExpr) {
    if (!arrayExpr) return "";

    std::ostringstream oss;

    // Get index expression
    const Expr* idx = arrayExpr->getIdx();
    std::string idxName;

    if (const DeclRefExpr* declRef = dyn_cast<DeclRefExpr>(idx->IgnoreImpCasts())) {
        idxName = declRef->getNameInfo().getAsString();
    } else {
        idxName = "idx"; // Generic name
    }

    // Try to determine bounds
    // For now, use generic bounds check
    // In a more sophisticated implementation, we would analyze the context
    // to determine the actual array size

    oss << "0 <= " << idxName;

    return oss.str();
}

std::string ACSLStatementAnnotator::extractNonZeroConstraint(const Expr *divisor) {
    if (!divisor) return "";

    std::ostringstream oss;

    // Get divisor name or expression
    std::string divisorName;
    if (const DeclRefExpr* declRef = dyn_cast<DeclRefExpr>(divisor->IgnoreImpCasts())) {
        divisorName = declRef->getNameInfo().getAsString();
    } else if (const MemberExpr* memberExpr = dyn_cast<MemberExpr>(divisor->IgnoreImpCasts())) {
        divisorName = memberExpr->getMemberNameInfo().getAsString();
    } else {
        divisorName = "divisor"; // Generic name
    }

    oss << divisorName << " != 0";

    return oss.str();
}

std::string ACSLStatementAnnotator::extractBufferConstraint(const Stmt *stmt) {
    if (!stmt) return "";

    // For buffer operations, we would need to analyze the arguments
    // to strcpy, memcpy, etc. and generate appropriate constraints
    // For now, return a generic constraint

    return "\\valid(buffer)";
}

std::string ACSLStatementAnnotator::extractCastConstraint(const CastExpr *castExpr) {
    if (!castExpr) return "";

    std::ostringstream oss;

    // For dynamic_cast, ensure result is not null
    if (isa<CXXDynamicCastExpr>(castExpr)) {
        oss << "\\valid(cast_result)";
    } else {
        // For other casts, ensure source is valid
        oss << "\\valid(cast_source)";
    }

    return oss.str();
}

// ============================================================================
// Context analysis methods
// ============================================================================

bool ACSLStatementAnnotator::hasValidationContext(const Stmt *stmt) {
    // Check if preceding statements contain validation logic
    // This would require control-flow analysis
    // For now, return false
    return false;
}

bool ACSLStatementAnnotator::isConstructorPostInit(const Stmt *stmt) {
    // Check if we're in a constructor after member initialization
    // This would require context tracking
    // For now, return false
    return false;
}

std::string ACSLStatementAnnotator::generateValidatedAssumption(const Stmt *stmt) {
    // Generate assume annotation for validated input
    return "";
}

std::string ACSLStatementAnnotator::generateConstructorAssumption(const Stmt *stmt) {
    // Generate assume annotation for constructor
    return "";
}

bool ACSLStatementAnnotator::isProofMilestone(const Stmt *stmt) {
    // Check if statement is a proof milestone
    // This would require pattern matching on comments or specific code patterns
    // For now, return false
    return false;
}

std::string ACSLStatementAnnotator::generateProofMilestoneCheck(const Stmt *stmt) {
    // Generate check annotation for proof milestone
    return "";
}

bool ACSLStatementAnnotator::maintainsInvariant(const Stmt *stmt) {
    // Check if statement should preserve invariant
    // This would require invariant tracking
    // For now, return false
    return false;
}

std::string ACSLStatementAnnotator::generateInvariantMaintenanceCheck(const Stmt *stmt) {
    // Generate check annotation for invariant maintenance
    return "";
}

// ============================================================================
// Helper methods
// ============================================================================

const Expr* ACSLStatementAnnotator::getStatementExpression(const Stmt *stmt) {
    if (!stmt) return nullptr;

    // Direct expression
    if (const Expr* expr = dyn_cast<Expr>(stmt)) {
        return expr;
    }

    // Return statement
    if (const ReturnStmt* retStmt = dyn_cast<ReturnStmt>(stmt)) {
        return retStmt->getRetValue();
    }

    // Declaration statement with initializer
    if (const DeclStmt* declStmt = dyn_cast<DeclStmt>(stmt)) {
        if (declStmt->isSingleDecl()) {
            if (const VarDecl* varDecl = dyn_cast<VarDecl>(declStmt->getSingleDecl())) {
                return varDecl->getInit();
            }
        }
    }

    // Binary operator
    if (const BinaryOperator* binOp = dyn_cast<BinaryOperator>(stmt)) {
        return binOp;
    }

    // Unary operator
    if (const UnaryOperator* unaryOp = dyn_cast<UnaryOperator>(stmt)) {
        return unaryOp;
    }

    return nullptr;
}

std::string ACSLStatementAnnotator::formatAnnotation(const std::string& annotation,
                                                     const Stmt *stmt) {
    // Apply proper indentation based on statement location
    // For now, just return the annotation as-is
    return annotation;
}
