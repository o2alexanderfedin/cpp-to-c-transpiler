// Phase 4 (v1.21.0): ACSL Ghost Code Injection Implementation
// Plan: .planning/phases/04-ghost-code/PLAN.md
//
// Implementation following SOLID and TDD principles

#include "ACSLGhostCodeInjector.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Type.h"
#include "clang/AST/OperationKinds.h"
#include <sstream>
#include <algorithm>

using namespace clang;

// ============================================================================
// Constructors
// ============================================================================

ACSLGhostCodeInjector::ACSLGhostCodeInjector()
    : ACSLGenerator(), m_ghostVarCounter(0) {
}

ACSLGhostCodeInjector::ACSLGhostCodeInjector(ACSLLevel level)
    : ACSLGenerator(level), m_ghostVarCounter(0) {
}

ACSLGhostCodeInjector::ACSLGhostCodeInjector(ACSLLevel level, ACSLOutputMode mode)
    : ACSLGenerator(level, mode), m_ghostVarCounter(0) {
}

// ============================================================================
// Main injection method
// ============================================================================

std::string ACSLGhostCodeInjector::injectGhostCode(const FunctionDecl* func) {
    if (!func || !func->hasBody()) {
        return "";
    }

    // Reset state
    m_declaredGhostVars.clear();
    m_ghostVarNames.clear();
    m_ghostVarCounter = 0;

    // Analyze function for ghost opportunities
    std::vector<GhostVariable> ghostVars = analyzeGhostOpportunities(func);

    if (ghostVars.empty()) {
        return "";
    }

    // Generate ghost code
    std::ostringstream oss;

    for (const auto& ghostVar : ghostVars) {
        // Generate declaration
        std::string decl = generateGhostDeclaration(ghostVar);
        if (!decl.empty()) {
            oss << decl << "\n";
        }

        // Track the ghost variable
        trackGhostVariable(ghostVar, ghostVar.scope);
    }

    return oss.str();
}

// ============================================================================
// Ghost opportunity analysis
// ============================================================================

std::vector<ACSLGhostCodeInjector::GhostVariable>
ACSLGhostCodeInjector::analyzeGhostOpportunities(const FunctionDecl* func) {
    if (!func) return {};

    GhostAnalysisVisitor visitor(this);
    visitor.TraverseStmt(func->getBody());

    return visitor.getGhostVariables();
}

// ============================================================================
// Ghost code generation
// ============================================================================

std::string ACSLGhostCodeInjector::generateGhostDeclaration(const GhostVariable& ghostVar) {
    std::ostringstream oss;

    oss << "//@ ghost " << ghostVar.type << " " << ghostVar.name;

    if (!ghostVar.initialValue.empty()) {
        oss << " = " << ghostVar.initialValue;
    }

    oss << ";";

    return oss.str();
}

std::string ACSLGhostCodeInjector::generateGhostAssignment(const GhostVariable& ghostVar,
                                                            const std::string& newValue) {
    std::ostringstream oss;

    oss << "//@ ghost " << ghostVar.name << " = " << newValue << ";";

    return oss.str();
}

std::string ACSLGhostCodeInjector::generateGhostBlock(
    const std::vector<std::string>& statements) {

    if (statements.empty()) {
        return "";
    }

    if (statements.size() == 1) {
        return statements[0];
    }

    std::ostringstream oss;
    oss << "//@ ghost {\n";

    for (const auto& stmt : statements) {
        oss << "//@   " << stmt << "\n";
    }

    oss << "//@ }";

    return oss.str();
}

// ============================================================================
// Ghost variable tracking
// ============================================================================

void ACSLGhostCodeInjector::trackGhostVariable(const GhostVariable& ghostVar,
                                                const Stmt* scope) {
    m_declaredGhostVars[ghostVar.name] = ghostVar;
    m_ghostVarNames.insert(ghostVar.name);
}

bool ACSLGhostCodeInjector::isGhostVariableInScope(const std::string& name,
                                                     const Stmt* stmt) {
    // Simple scope check: if declared, it's in scope
    // Full implementation would track statement hierarchy
    return m_ghostVarNames.find(name) != m_ghostVarNames.end();
}

// ============================================================================
// GhostAnalysisVisitor implementation
// ============================================================================

bool ACSLGhostCodeInjector::GhostAnalysisVisitor::VisitForStmt(ForStmt* stmt) {
    if (!stmt) return true;

    // Analyze loop body for accumulator patterns
    if (Stmt* body = stmt->getBody()) {
        // Check for sum pattern
        if (GhostVariable* sumGhost = m_injector->detectSumTracking(body)) {
            m_ghostVariables.push_back(*sumGhost);
            delete sumGhost;
        }

        // Check for count pattern
        if (GhostVariable* countGhost = m_injector->detectCountTracking(body)) {
            m_ghostVariables.push_back(*countGhost);
            delete countGhost;
        }

        // Check for max pattern
        if (GhostVariable* maxGhost = m_injector->detectMaxTracking(body)) {
            m_ghostVariables.push_back(*maxGhost);
            delete maxGhost;
        }

        // Check for min pattern
        if (GhostVariable* minGhost = m_injector->detectMinTracking(body)) {
            m_ghostVariables.push_back(*minGhost);
            delete minGhost;
        }
    }

    return true;
}

bool ACSLGhostCodeInjector::GhostAnalysisVisitor::VisitWhileStmt(WhileStmt* stmt) {
    if (!stmt) return true;

    // Similar analysis for while loops
    if (Stmt* body = stmt->getBody()) {
        if (GhostVariable* sumGhost = m_injector->detectSumTracking(body)) {
            m_ghostVariables.push_back(*sumGhost);
            delete sumGhost;
        }

        if (GhostVariable* countGhost = m_injector->detectCountTracking(body)) {
            m_ghostVariables.push_back(*countGhost);
            delete countGhost;
        }
    }

    return true;
}

bool ACSLGhostCodeInjector::GhostAnalysisVisitor::VisitBinaryOperator(BinaryOperator* op) {
    if (!op) return true;

    // Detect assignment patterns
    if (op->getOpcode() == BO_Assign) {
        // Check for value mutations
        if (GhostVariable* prevGhost = m_injector->detectPreviousValueTracking(op)) {
            m_ghostVariables.push_back(*prevGhost);
            delete prevGhost;
        }
    }

    return true;
}

bool ACSLGhostCodeInjector::GhostAnalysisVisitor::VisitVarDecl(VarDecl* decl) {
    if (!decl) return true;

    // Track variable declarations for potential ghost variables
    // This helps identify accumulators, counters, etc.

    return true;
}

bool ACSLGhostCodeInjector::GhostAnalysisVisitor::VisitArraySubscriptExpr(
    ArraySubscriptExpr* expr) {

    if (!expr) return true;

    // Detect array modifications that might need snapshots
    // Check if this is a write (LHS of assignment)

    return true;
}

// ============================================================================
// Pattern detection methods
// ============================================================================

ACSLGhostCodeInjector::GhostVariable*
ACSLGhostCodeInjector::detectMaxTracking(const Stmt* stmt) {
    if (!stmt) return nullptr;

    // Look for pattern: if (x > max) max = x;
    if (const IfStmt* ifStmt = dyn_cast<IfStmt>(stmt)) {
        if (const BinaryOperator* cond = dyn_cast_or_null<BinaryOperator>(ifStmt->getCond())) {
            if (cond->getOpcode() == BO_GT || cond->getOpcode() == BO_GE) {
                // Found comparison pattern
                std::string name = ensureUniqueName("ghost_max");
                std::string type = "int";
                std::string init = "0";

                return new GhostVariable(name, type, init, stmt, GhostPurpose::MaxTracking);
            }
        }
    }

    // Recursively check children
    for (const Stmt* child : stmt->children()) {
        if (GhostVariable* result = detectMaxTracking(child)) {
            return result;
        }
    }

    return nullptr;
}

ACSLGhostCodeInjector::GhostVariable*
ACSLGhostCodeInjector::detectMinTracking(const Stmt* stmt) {
    if (!stmt) return nullptr;

    // Look for pattern: if (x < min) min = x;
    if (const IfStmt* ifStmt = dyn_cast<IfStmt>(stmt)) {
        if (const BinaryOperator* cond = dyn_cast_or_null<BinaryOperator>(ifStmt->getCond())) {
            if (cond->getOpcode() == BO_LT || cond->getOpcode() == BO_LE) {
                std::string name = ensureUniqueName("ghost_min");
                std::string type = "int";
                std::string init = "0";

                return new GhostVariable(name, type, init, stmt, GhostPurpose::MinTracking);
            }
        }
    }

    return nullptr;
}

ACSLGhostCodeInjector::GhostVariable*
ACSLGhostCodeInjector::detectSumTracking(const Stmt* stmt) {
    if (!stmt) return nullptr;

    // Look for pattern: sum += x or sum = sum + x
    if (const BinaryOperator* binOp = dyn_cast<BinaryOperator>(stmt)) {
        if (binOp->getOpcode() == BO_AddAssign || binOp->getOpcode() == BO_Add) {
            // Check if LHS is named "sum" or similar
            if (const DeclRefExpr* lhs = dyn_cast<DeclRefExpr>(binOp->getLHS())) {
                std::string varName = lhs->getNameInfo().getAsString();
                if (varName.find("sum") != std::string::npos ||
                    varName.find("total") != std::string::npos) {

                    std::string name = ensureUniqueName("ghost_sum");
                    std::string type = "int";
                    std::string init = "0";

                    return new GhostVariable(name, type, init, stmt, GhostPurpose::SumTracking);
                }
            }
        }
    }

    // Recursively check compound statements
    if (const CompoundStmt* compound = dyn_cast<CompoundStmt>(stmt)) {
        for (const Stmt* child : compound->children()) {
            if (GhostVariable* result = detectSumTracking(child)) {
                return result;
            }
        }
    }

    return nullptr;
}

ACSLGhostCodeInjector::GhostVariable*
ACSLGhostCodeInjector::detectCountTracking(const Stmt* stmt) {
    if (!stmt) return nullptr;

    // Look for pattern: count++ or count += 1
    if (const UnaryOperator* unaryOp = dyn_cast<UnaryOperator>(stmt)) {
        if (unaryOp->getOpcode() == UO_PostInc || unaryOp->getOpcode() == UO_PreInc) {
            if (const DeclRefExpr* subExpr = dyn_cast<DeclRefExpr>(unaryOp->getSubExpr())) {
                std::string varName = subExpr->getNameInfo().getAsString();
                if (varName.find("count") != std::string::npos ||
                    varName.find("counter") != std::string::npos) {

                    std::string name = ensureUniqueName("ghost_count");
                    std::string type = "int";
                    std::string init = "0";

                    return new GhostVariable(name, type, init, stmt, GhostPurpose::CountTracking);
                }
            }
        }
    }

    // Recursively check compound statements
    if (const CompoundStmt* compound = dyn_cast<CompoundStmt>(stmt)) {
        for (const Stmt* child : compound->children()) {
            if (GhostVariable* result = detectCountTracking(child)) {
                return result;
            }
        }
    }

    return nullptr;
}

ACSLGhostCodeInjector::GhostVariable*
ACSLGhostCodeInjector::detectPreviousValueTracking(const Stmt* stmt) {
    if (!stmt) return nullptr;

    // Detect when we need to track the old value before assignment
    if (const BinaryOperator* binOp = dyn_cast<BinaryOperator>(stmt)) {
        if (binOp->getOpcode() == BO_Assign) {
            // For any assignment, we might want to track old value
            // This is conservative - in practice, filter based on context
            std::string name = ensureUniqueName("ghost_old");
            std::string type = "int";
            std::string init = "";

            return new GhostVariable(name, type, init, stmt, GhostPurpose::PreviousValue);
        }
    }

    return nullptr;
}

ACSLGhostCodeInjector::GhostVariable*
ACSLGhostCodeInjector::detectArrayCopyTracking(const Stmt* stmt) {
    if (!stmt) return nullptr;

    // Detect array modifications requiring snapshot
    // Look for array assignments in loops
    if (const BinaryOperator* binOp = dyn_cast<BinaryOperator>(stmt)) {
        if (binOp->getOpcode() == BO_Assign) {
            if (const ArraySubscriptExpr* arrayExpr =
                dyn_cast<ArraySubscriptExpr>(binOp->getLHS())) {

                std::string name = ensureUniqueName("ghost_arr_copy");
                std::string type = "int*"; // Simplified
                std::string init = "";

                return new GhostVariable(name, type, init, stmt, GhostPurpose::ArrayCopy);
            }
        }
    }

    return nullptr;
}

// ============================================================================
// Helper methods
// ============================================================================

std::string ACSLGhostCodeInjector::getACSLType(QualType type) {
    if (type->isIntegerType()) {
        return "int"; // Use ACSL integer for unbounded math
    } else if (type->isFloatingType()) {
        return "real";
    } else if (type->isBooleanType()) {
        return "boolean";
    } else if (type->isPointerType()) {
        QualType pointeeType = type->getPointeeType();
        return getACSLType(pointeeType) + "*";
    } else if (type->isArrayType()) {
        if (const ConstantArrayType* arrayType = dyn_cast<ConstantArrayType>(type.getTypePtr())) {
            QualType elementType = arrayType->getElementType();
            return getACSLType(elementType) + "[]";
        }
        return "int[]";
    }

    return "int"; // Default fallback
}

std::string ACSLGhostCodeInjector::convertToACSLExpr(const Expr* expr) {
    if (!expr) return "";

    // Simplified expression conversion
    // Full implementation would recursively convert all expression types

    if (const IntegerLiteral* intLit = dyn_cast<IntegerLiteral>(expr)) {
        return std::to_string(intLit->getValue().getSExtValue());
    }

    if (const DeclRefExpr* declRef = dyn_cast<DeclRefExpr>(expr)) {
        return declRef->getNameInfo().getAsString();
    }

    if (const BinaryOperator* binOp = dyn_cast<BinaryOperator>(expr)) {
        std::string lhs = convertToACSLExpr(binOp->getLHS());
        std::string rhs = convertToACSLExpr(binOp->getRHS());
        std::string op;

        switch (binOp->getOpcode()) {
            case BO_Add: op = " + "; break;
            case BO_Sub: op = " - "; break;
            case BO_Mul: op = " * "; break;
            case BO_Div: op = " / "; break;
            case BO_Rem: op = " % "; break;
            case BO_GT:  op = " > "; break;
            case BO_LT:  op = " < "; break;
            case BO_GE:  op = " >= "; break;
            case BO_LE:  op = " <= "; break;
            case BO_EQ:  op = " == "; break;
            case BO_NE:  op = " != "; break;
            default: op = " ??? "; break;
        }

        return lhs + op + rhs;
    }

    return "";
}

std::string ACSLGhostCodeInjector::ensureUniqueName(const std::string& name) {
    if (m_ghostVarNames.find(name) == m_ghostVarNames.end()) {
        return name;
    }

    // Append counter to make unique
    std::string uniqueName;
    do {
        uniqueName = name + "_" + std::to_string(m_ghostVarCounter++);
    } while (m_ghostVarNames.find(uniqueName) != m_ghostVarNames.end());

    return uniqueName;
}

std::string ACSLGhostCodeInjector::formatGhostCode(const std::string& code,
                                                    unsigned indent) {
    std::string indentStr(indent, ' ');
    std::ostringstream oss;

    // Apply indentation to each line
    std::istringstream iss(code);
    std::string line;
    while (std::getline(iss, line)) {
        oss << indentStr << line << "\n";
    }

    return oss.str();
}
