// Phase 5 (v1.22.0): ACSL Function Behaviors
// Plan: .planning/phases/05-function-behaviors/PLAN.md
//
// Implementation following SOLID and TDD principles

#include "ACSLBehaviorAnnotator.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <sstream>
#include <algorithm>
#include <set>

using namespace clang;

// Constructors
ACSLBehaviorAnnotator::ACSLBehaviorAnnotator()
    : ACSLGenerator() {
}

ACSLBehaviorAnnotator::ACSLBehaviorAnnotator(ACSLLevel level)
    : ACSLGenerator(level) {
}

// Forward declaration for visitor friendship
class BehaviorExtractor;

// AST Visitor to extract behaviors from function body
class BehaviorExtractor : public RecursiveASTVisitor<BehaviorExtractor> {
public:
    std::vector<Behavior> behaviors;
    std::vector<const Expr*> conditions;
    ACSLBehaviorAnnotator* annotator;

    explicit BehaviorExtractor(ACSLBehaviorAnnotator* ann) : annotator(ann) {}

    // Helper methods - now part of visitor to access annotator protected methods
    std::string generateBehaviorName(const Expr* condition) {
        return annotator->generateBehaviorName(condition);
    }

    std::string generateAssumesClause(const Expr* condition) {
        return annotator->generateAssumesClause(condition);
    }

    std::string generateEnsuresForBehavior(const FunctionDecl* func,
                                            const Behavior& behavior,
                                            const ReturnStmt* returnStmt) {
        return annotator->generateEnsuresForBehavior(func, behavior, returnStmt);
    }

    const ReturnStmt* extractReturnFromBranch(const IfStmt* ifStmt) {
        return annotator->extractReturnFromBranch(ifStmt);
    }

    // Helper to detect if there's a return statement following this if
    const ReturnStmt* findReturnAfterIf(IfStmt* ifStmt) {
        // This would require parent traversal, which is complex
        // For now, we'll handle this differently in the visitor
        return nullptr;
    }

    bool VisitIfStmt(IfStmt* ifStmt) {
        if (!ifStmt) return true;

        Expr* condition = ifStmt->getCond();
        if (!condition) return true;

        // Extract behavior from if branch
        Behavior thenBehavior;
        thenBehavior.name = generateBehaviorName(condition);
        thenBehavior.assumesClause = generateAssumesClause(condition);

        // Try to find return statement in then branch
        const ReturnStmt* thenReturn = extractReturnFromBranch(ifStmt);
        if (thenReturn) {
            std::string ensures = generateEnsuresForBehavior(nullptr, thenBehavior, thenReturn);
            if (!ensures.empty()) {
                thenBehavior.ensuresClauses.push_back(ensures);
            }
        }

        if (!thenBehavior.assumesClause.empty()) {
            behaviors.push_back(thenBehavior);
            conditions.push_back(condition);
        }

        // Extract behavior from else branch if present
        if (const Stmt* elseStmt = ifStmt->getElse()) {
            // If else is not another IfStmt, create complementary behavior
            if (!isa<IfStmt>(elseStmt)) {
                Behavior elseBehavior;
                elseBehavior.name = "else_" + thenBehavior.name;
                // Negate the condition for else branch
                elseBehavior.assumesClause = "!(" + thenBehavior.assumesClause + ")";

                // Look for return in else branch
                if (auto* compoundStmt = dyn_cast<CompoundStmt>(elseStmt)) {
                    for (auto* stmt : compoundStmt->body()) {
                        if (auto* retStmt = dyn_cast<ReturnStmt>(stmt)) {
                            std::string ensures = generateEnsuresForBehavior(nullptr, elseBehavior, retStmt);
                            if (!ensures.empty()) {
                                elseBehavior.ensuresClauses.push_back(ensures);
                            }
                            break;
                        }
                    }
                } else if (auto* retStmt = dyn_cast<ReturnStmt>(elseStmt)) {
                    std::string ensures = generateEnsuresForBehavior(nullptr, elseBehavior, retStmt);
                    if (!ensures.empty()) {
                        elseBehavior.ensuresClauses.push_back(ensures);
                    }
                }

                if (!elseBehavior.assumesClause.empty()) {
                    behaviors.push_back(elseBehavior);
                }
            }
        }

        return true;
    }

    bool VisitSwitchStmt(SwitchStmt* switchStmt) {
        if (!switchStmt) return true;

        // Extract condition variable
        Expr* conditionExpr = switchStmt->getCond();
        if (!conditionExpr) return true;

        // Traverse switch body to find cases
        Stmt* body = switchStmt->getBody();
        if (!body) return true;

        if (auto* compoundStmt = dyn_cast<CompoundStmt>(body)) {
            const CaseStmt* currentCase = nullptr;
            std::vector<Stmt*> caseStmts;

            for (auto* stmt : compoundStmt->body()) {
                if (auto* caseStmt = dyn_cast<CaseStmt>(stmt)) {
                    // Process previous case if any
                    if (currentCase && !caseStmts.empty()) {
                        Behavior behavior;
                        behavior.name = "case_" + annotator->convertExprToACSL(currentCase->getLHS());
                        behavior.assumesClause = annotator->convertExprToACSL(conditionExpr) + " == " +
                                                 annotator->convertExprToACSL(currentCase->getLHS());

                        // Look for return in case statements
                        for (auto* caseBodyStmt : caseStmts) {
                            if (auto* retStmt = dyn_cast<ReturnStmt>(caseBodyStmt)) {
                                std::string ensures = generateEnsuresForBehavior(nullptr, behavior, retStmt);
                                if (!ensures.empty()) {
                                    behavior.ensuresClauses.push_back(ensures);
                                }
                                break;
                            }
                        }

                        if (!behavior.assumesClause.empty()) {
                            behaviors.push_back(behavior);
                            conditions.push_back(conditionExpr);
                        }
                    }

                    // Start new case
                    currentCase = caseStmt;
                    caseStmts.clear();
                } else if (auto* defaultStmt = dyn_cast<DefaultStmt>(stmt)) {
                    // Process previous case if any
                    if (currentCase && !caseStmts.empty()) {
                        Behavior behavior;
                        behavior.name = "case_" + annotator->convertExprToACSL(currentCase->getLHS());
                        behavior.assumesClause = annotator->convertExprToACSL(conditionExpr) + " == " +
                                                 annotator->convertExprToACSL(currentCase->getLHS());

                        for (auto* caseBodyStmt : caseStmts) {
                            if (auto* retStmt = dyn_cast<ReturnStmt>(caseBodyStmt)) {
                                std::string ensures = generateEnsuresForBehavior(nullptr, behavior, retStmt);
                                if (!ensures.empty()) {
                                    behavior.ensuresClauses.push_back(ensures);
                                }
                                break;
                            }
                        }

                        if (!behavior.assumesClause.empty()) {
                            behaviors.push_back(behavior);
                        }
                    }

                    // Handle default case
                    currentCase = nullptr;
                    caseStmts.clear();

                    // Look for return in default
                    Stmt* defaultBody = defaultStmt->getSubStmt();
                    if (defaultBody) {
                        if (auto* retStmt = dyn_cast<ReturnStmt>(defaultBody)) {
                            Behavior behavior;
                            behavior.name = "default_case";
                            behavior.assumesClause = "true"; // default covers all other cases
                            std::string ensures = generateEnsuresForBehavior(nullptr, behavior, retStmt);
                            if (!ensures.empty()) {
                                behavior.ensuresClauses.push_back(ensures);
                            }
                            behaviors.push_back(behavior);
                            conditions.push_back(conditionExpr);
                        }
                    }
                } else if (currentCase) {
                    // Statement is part of current case
                    caseStmts.push_back(stmt);
                }
            }

            // Process final case if any
            if (currentCase && !caseStmts.empty()) {
                Behavior behavior;
                behavior.name = "case_" + annotator->convertExprToACSL(currentCase->getLHS());
                behavior.assumesClause = annotator->convertExprToACSL(conditionExpr) + " == " +
                                         annotator->convertExprToACSL(currentCase->getLHS());

                for (auto* caseBodyStmt : caseStmts) {
                    if (auto* retStmt = dyn_cast<ReturnStmt>(caseBodyStmt)) {
                        std::string ensures = generateEnsuresForBehavior(nullptr, behavior, retStmt);
                        if (!ensures.empty()) {
                            behavior.ensuresClauses.push_back(ensures);
                        }
                        break;
                    }
                }

                if (!behavior.assumesClause.empty()) {
                    behaviors.push_back(behavior);
                    conditions.push_back(conditionExpr);
                }
            }
        }

        return true;
    }
};

// Generate behaviors from function
std::string ACSLBehaviorAnnotator::generateBehaviors(const FunctionDecl* func) {
    if (!func || !func->hasBody()) {
        return "";
    }

    // Extract behaviors from control flow
    BehaviorExtractor extractor(this);
    extractor.TraverseStmt(func->getBody());

    if (extractor.behaviors.empty()) {
        return "";
    }

    // Check completeness and disjointness
    bool isComplete = checkCompleteness(func);
    bool isDisjoint = checkDisjointness(func);

    // Format as ACSL annotation
    return formatBehaviors(extractor.behaviors, isComplete, isDisjoint);
}

// Check completeness
bool ACSLBehaviorAnnotator::checkCompleteness(const FunctionDecl* func) {
    if (!func || !func->hasBody()) {
        return false;
    }

    BehaviorExtractor extractor(this);
    extractor.TraverseStmt(func->getBody());

    if (extractor.behaviors.empty()) {
        return false;
    }

    // Check for explicit completeness indicators:

    // 1. If we have else_* behavior, it's from if/else → complete
    for (const auto& behavior : extractor.behaviors) {
        if (behavior.name.find("else_") == 0) {
            return true;
        }
    }

    // 2. If we have default_case from switch → complete
    for (const auto& behavior : extractor.behaviors) {
        if (behavior.name == "default_case") {
            return true;
        }
    }

    // 3. Single if with early return pattern: if (cond) return; return;
    //    This is complete even though no explicit else
    if (extractor.behaviors.size() == 1 && !extractor.behaviors[0].ensuresClauses.empty()) {
        // Heuristic: single behavior with ensures likely has fallthrough return
        // Check if function always returns (would need control flow analysis)
        // For now, assume complete
        return true;
    }

    // 4. Otherwise, incomplete (multiple ifs without full coverage)
    return false;
}

// Check disjointness
bool ACSLBehaviorAnnotator::checkDisjointness(const FunctionDecl* func) {
    if (!func || !func->hasBody()) {
        return true; // Vacuously true
    }

    BehaviorExtractor extractor(this);
    extractor.TraverseStmt(func->getBody());

    // Check pairwise for overlaps
    for (size_t i = 0; i < extractor.conditions.size(); ++i) {
        for (size_t j = i + 1; j < extractor.conditions.size(); ++j) {
            if (conditionsOverlap(extractor.conditions[i], extractor.conditions[j])) {
                return false;
            }
        }
    }

    return true;
}

// Extract behaviors from if/else
std::vector<Behavior> ACSLBehaviorAnnotator::extractBehaviorsFromIfElse(const FunctionDecl* func) {
    std::vector<Behavior> behaviors;

    if (!func || !func->hasBody()) {
        return behaviors;
    }

    BehaviorExtractor extractor(this);
    extractor.TraverseStmt(func->getBody());

    return extractor.behaviors;
}

// Extract behaviors from switch
std::vector<Behavior> ACSLBehaviorAnnotator::extractBehaviorsFromSwitch(const FunctionDecl* func) {
    std::vector<Behavior> behaviors;

    if (!func || !func->hasBody()) {
        return behaviors;
    }

    // TODO: Implement switch case extraction
    // Would traverse SwitchStmt and create behavior for each case

    return behaviors;
}

// Extract behaviors from nested conditions
std::vector<Behavior> ACSLBehaviorAnnotator::extractBehaviorsFromNestedConditions(const FunctionDecl* func) {
    // Nested conditions handled by BehaviorExtractor traversal
    return extractBehaviorsFromIfElse(func);
}

// Generate assumes clause from condition
std::string ACSLBehaviorAnnotator::generateAssumesClause(const Expr* condition) {
    if (!condition) {
        return "";
    }

    return convertExprToACSL(condition);
}

// Generate ensures clause for behavior
std::string ACSLBehaviorAnnotator::generateEnsuresForBehavior(const FunctionDecl* func,
                                                               const Behavior& behavior,
                                                               const ReturnStmt* returnStmt) {
    if (!returnStmt) {
        return "";
    }

    const Expr* returnValue = returnStmt->getRetValue();
    if (!returnValue) {
        return "";
    }

    std::ostringstream oss;
    oss << "\\result == " << convertExprToACSL(returnValue);
    return oss.str();
}

// Detect error behavior
bool ACSLBehaviorAnnotator::isErrorBehavior(const Behavior& behavior) {
    // Check for common error patterns
    std::string assumes = behavior.assumesClause;

    // Null checks
    if (assumes.find("\\null") != std::string::npos ||
        assumes.find("nullptr") != std::string::npos) {
        return true;
    }

    // Zero divisor
    if (assumes.find("== 0") != std::string::npos) {
        return true;
    }

    // Check ensures for error return values
    for (const auto& ensures : behavior.ensuresClauses) {
        if (ensures.find("\\result == -1") != std::string::npos ||
            ensures.find("\\result == \\null") != std::string::npos) {
            return true;
        }
    }

    return false;
}

// Detect normal behavior
bool ACSLBehaviorAnnotator::isNormalBehavior(const Behavior& behavior) {
    return !isErrorBehavior(behavior);
}

// Generate behavior name
std::string ACSLBehaviorAnnotator::generateBehaviorName(const Expr* condition) {
    if (!condition) {
        return "default";
    }

    // Check for null checks
    if (isNullCheck(condition)) {
        return "null_check";
    }

    // Check for range checks
    if (isRangeCheck(condition)) {
        return "range_check";
    }

    // Extract variable name if possible
    if (auto* binaryOp = dyn_cast<BinaryOperator>(condition)) {
        if (auto* declRef = dyn_cast<DeclRefExpr>(binaryOp->getLHS()->IgnoreImpCasts())) {
            std::string varName = declRef->getNameInfo().getAsString();

            switch (binaryOp->getOpcode()) {
                case BO_EQ:
                    return varName + "_equal";
                case BO_NE:
                    return varName + "_not_equal";
                case BO_LT:
                    return varName + "_less";
                case BO_GT:
                    return varName + "_greater";
                case BO_LE:
                    return varName + "_less_equal";
                case BO_GE:
                    return varName + "_greater_equal";
                default:
                    return varName + "_cond";
            }
        }
    }

    return "behavior";
}

// Format behaviors as ACSL
std::string ACSLBehaviorAnnotator::formatBehaviors(const std::vector<Behavior>& behaviors,
                                                    bool isComplete,
                                                    bool isDisjoint) {
    if (behaviors.empty()) {
        return "";
    }

    std::ostringstream oss;

    // Generate each behavior (no leading spaces - formatACSLComment adds them)
    for (const auto& behavior : behaviors) {
        oss << "behavior " << behavior.name << ":\n";
        oss << "  assumes " << behavior.assumesClause << ";\n";

        for (const auto& ensures : behavior.ensuresClauses) {
            oss << "  ensures " << ensures << ";\n";
        }
    }

    // Add completeness/disjointness clauses
    if (isComplete) {
        oss << "complete behaviors;";
        if (isDisjoint) {
            oss << "\n";
        }
    }
    if (isDisjoint) {
        oss << "disjoint behaviors;";
    }

    return formatACSLComment(oss.str());
}

// Convert C++ expression to ACSL
std::string ACSLBehaviorAnnotator::convertExprToACSL(const Expr* expr) {
    if (!expr) {
        return "";
    }

    std::ostringstream oss;

    // Handle different expression types
    if (auto* binaryOp = dyn_cast<BinaryOperator>(expr)) {
        std::string lhs = convertExprToACSL(binaryOp->getLHS());
        std::string rhs = convertExprToACSL(binaryOp->getRHS());

        switch (binaryOp->getOpcode()) {
            case BO_EQ:
                oss << lhs << " == " << rhs;
                break;
            case BO_NE:
                oss << lhs << " != " << rhs;
                break;
            case BO_LT:
                oss << lhs << " < " << rhs;
                break;
            case BO_GT:
                oss << lhs << " > " << rhs;
                break;
            case BO_LE:
                oss << lhs << " <= " << rhs;
                break;
            case BO_GE:
                oss << lhs << " >= " << rhs;
                break;
            case BO_LAnd:
                oss << lhs << " && " << rhs;
                break;
            case BO_LOr:
                oss << lhs << " || " << rhs;
                break;
            default:
                oss << lhs << " <op> " << rhs;
                break;
        }
    } else if (auto* declRef = dyn_cast<DeclRefExpr>(expr)) {
        oss << declRef->getNameInfo().getAsString();
    } else if (auto* intLit = dyn_cast<IntegerLiteral>(expr)) {
        llvm::SmallString<32> str;
        intLit->getValue().toString(str, 10, intLit->getType()->isSignedIntegerType());
        oss << str.str().str();
    } else if (auto* cxxNullPtr = dyn_cast<CXXNullPtrLiteralExpr>(expr)) {
        oss << "\\null";
    } else if (auto* implicitCast = dyn_cast<ImplicitCastExpr>(expr)) {
        return convertExprToACSL(implicitCast->getSubExpr());
    } else if (auto* parenExpr = dyn_cast<ParenExpr>(expr)) {
        oss << "(" << convertExprToACSL(parenExpr->getSubExpr()) << ")";
    } else if (auto* unaryOp = dyn_cast<UnaryOperator>(expr)) {
        if (unaryOp->getOpcode() == UO_LNot) {
            oss << "!(" << convertExprToACSL(unaryOp->getSubExpr()) << ")";
        } else if (unaryOp->getOpcode() == UO_Deref) {
            oss << "*" << convertExprToACSL(unaryOp->getSubExpr());
        } else {
            oss << convertExprToACSL(unaryOp->getSubExpr());
        }
    } else {
        // Default: try to get source text
        oss << "expr";
    }

    return oss.str();
}

// Check if conditions overlap
bool ACSLBehaviorAnnotator::conditionsOverlap(const Expr* cond1, const Expr* cond2) {
    if (!cond1 || !cond2) {
        return false;
    }

    // Simple overlap detection based on expression structure
    // More sophisticated: Would use SMT solver

    // Check if conditions are the same
    std::string acsl1 = convertExprToACSL(cond1);
    std::string acsl2 = convertExprToACSL(cond2);

    if (acsl1 == acsl2) {
        return true;
    }

    // Check for obvious overlaps like (x > 0) and (x >= 0)
    if (auto* bin1 = dyn_cast<BinaryOperator>(cond1)) {
        if (auto* bin2 = dyn_cast<BinaryOperator>(cond2)) {
            // Same LHS variable
            std::string lhs1 = convertExprToACSL(bin1->getLHS());
            std::string lhs2 = convertExprToACSL(bin2->getLHS());

            if (lhs1 == lhs2) {
                // Check for overlapping comparisons
                BinaryOperatorKind op1 = bin1->getOpcode();
                BinaryOperatorKind op2 = bin2->getOpcode();

                // (x > 0) and (x >= 0) overlap
                if ((op1 == BO_GT && op2 == BO_GE) ||
                    (op1 == BO_GE && op2 == BO_GT)) {
                    return true;
                }

                // (x < 0) and (x <= 0) overlap
                if ((op1 == BO_LT && op2 == BO_LE) ||
                    (op1 == BO_LE && op2 == BO_LT)) {
                    return true;
                }
            }
        }
    }

    return false;
}

// Check if conditions are exhaustive
bool ACSLBehaviorAnnotator::conditionsAreExhaustive(const std::vector<const Expr*>& conditions) {
    if (conditions.empty()) {
        return false;
    }

    // Simple heuristic: If we extracted behaviors, they're likely from if/else structures
    // which are complete. More sophisticated analysis would use SMT solver.
    // For now, assume behaviors from if/else are complete if we have at least one condition
    // This is a simplification but works for common patterns.

    // If we have extracted behaviors, assume completeness
    // This matches the pattern where BehaviorExtractor creates complementary behaviors
    // for if/else structures (including else_* behaviors)
    return conditions.size() >= 1;
}

// Extract return from branch
const ReturnStmt* ACSLBehaviorAnnotator::extractReturnFromBranch(const IfStmt* ifStmt) {
    if (!ifStmt) {
        return nullptr;
    }

    const Stmt* thenStmt = ifStmt->getThen();
    if (!thenStmt) {
        return nullptr;
    }

    // Direct return
    if (auto* retStmt = dyn_cast<ReturnStmt>(thenStmt)) {
        return retStmt;
    }

    // Return in compound statement
    if (auto* compoundStmt = dyn_cast<CompoundStmt>(thenStmt)) {
        for (auto* stmt : compoundStmt->body()) {
            if (auto* retStmt = dyn_cast<ReturnStmt>(stmt)) {
                return retStmt;
            }
        }
    }

    return nullptr;
}

// Check if expression is null check
bool ACSLBehaviorAnnotator::isNullCheck(const Expr* expr) {
    if (!expr) {
        return false;
    }

    if (auto* binaryOp = dyn_cast<BinaryOperator>(expr)) {
        // Check for ptr == nullptr or ptr != nullptr
        if (binaryOp->getOpcode() == BO_EQ || binaryOp->getOpcode() == BO_NE) {
            const Expr* rhs = binaryOp->getRHS()->IgnoreImpCasts();
            if (isa<CXXNullPtrLiteralExpr>(rhs) ||
                (isa<ImplicitCastExpr>(rhs) &&
                 isa<CXXNullPtrLiteralExpr>(cast<ImplicitCastExpr>(rhs)->getSubExpr()))) {
                return true;
            }
        }
    }

    return false;
}

// Check if expression is range check
bool ACSLBehaviorAnnotator::isRangeCheck(const Expr* expr) {
    if (!expr) {
        return false;
    }

    if (auto* binaryOp = dyn_cast<BinaryOperator>(expr)) {
        BinaryOperatorKind op = binaryOp->getOpcode();
        return (op == BO_LT || op == BO_GT || op == BO_LE || op == BO_GE);
    }

    return false;
}
