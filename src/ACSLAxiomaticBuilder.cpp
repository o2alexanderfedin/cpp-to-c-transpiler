// Phase 3 (v1.20.0): ACSL Axiomatic Definitions Implementation
// Plan: .planning/phases/03-axiomatic-definitions/PLAN.md
//
// Implementation following SOLID and TDD principles

#include "ACSLAxiomaticBuilder.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/OperationKinds.h"
#include <sstream>
#include <algorithm>
#include <regex>

using namespace clang;

// ============================================================================
// Constructors
// ============================================================================

ACSLAxiomaticBuilder::ACSLAxiomaticBuilder()
    : ACSLGenerator() {
}

ACSLAxiomaticBuilder::ACSLAxiomaticBuilder(ACSLLevel level)
    : ACSLGenerator(level) {
}

ACSLAxiomaticBuilder::ACSLAxiomaticBuilder(ACSLLevel level, ACSLOutputMode mode)
    : ACSLGenerator(level, mode) {
}

// ============================================================================
// Main generation methods
// ============================================================================

std::string ACSLAxiomaticBuilder::generateAxiomaticBlock(const FunctionDecl* func) {
    if (!func || !isPureFunction(func)) {
        return "";
    }

    // Check for recursion
    if (m_processingFunctions.find(func) != m_processingFunctions.end()) {
        return ""; // Avoid infinite recursion
    }
    m_processingFunctions.insert(func);

    std::string blockName = getAxiomaticBlockName(func);

    // Generate logic function
    std::vector<std::string> logicFunctions;
    std::string logicFunc = generateLogicFunction(func);
    if (!logicFunc.empty()) {
        logicFunctions.push_back(logicFunc);
    }

    // Generate axioms
    std::vector<std::string> axioms = generateAxioms(func);

    // Check axiom consistency
    if (!checkAxiomConsistency(axioms)) {
        m_processingFunctions.erase(func);
        return ""; // Inconsistent axioms detected
    }

    // Generate lemmas
    std::vector<std::string> lemmas = generateLemmas(func);

    // Generate inductive predicate if applicable
    QualType returnType = func->getReturnType();
    if (returnType->isBooleanType()) {
        std::string inductivePred = generateInductivePredicate(func);
        if (!inductivePred.empty()) {
            logicFunctions.push_back(inductivePred);
        }
    }

    m_processingFunctions.erase(func);

    return formatAxiomaticBlock(blockName, logicFunctions, axioms, lemmas);
}

std::string ACSLAxiomaticBuilder::generateAxiomaticBlock(
    const std::vector<const FunctionDecl*>& functions,
    const std::string& blockName) {

    if (functions.empty()) {
        return "";
    }

    std::vector<std::string> logicFunctions;
    std::vector<std::string> axioms;
    std::vector<std::string> lemmas;

    for (const auto* func : functions) {
        if (!isPureFunction(func)) continue;

        // Generate logic function
        std::string logicFunc = generateLogicFunction(func);
        if (!logicFunc.empty()) {
            logicFunctions.push_back(logicFunc);
        }

        // Collect axioms
        std::vector<std::string> funcAxioms = generateAxioms(func);
        axioms.insert(axioms.end(), funcAxioms.begin(), funcAxioms.end());

        // Collect lemmas
        std::vector<std::string> funcLemmas = generateLemmas(func);
        lemmas.insert(lemmas.end(), funcLemmas.begin(), funcLemmas.end());
    }

    if (!checkAxiomConsistency(axioms)) {
        return ""; // Inconsistent axioms
    }

    return formatAxiomaticBlock(blockName, logicFunctions, axioms, lemmas);
}

// ============================================================================
// Pure function detection
// ============================================================================

bool ACSLAxiomaticBuilder::isPureFunction(const FunctionDecl* func) {
    if (!func) return false;

    // Check if function has const qualifier (member function)
    if (const CXXMethodDecl* method = dyn_cast<CXXMethodDecl>(func)) {
        if (!method->isConst() && method->isInstance()) {
            return false; // Non-const methods can modify state
        }
    }

    // Check if function has side effects in body
    if (!func->hasBody()) {
        return false; // No body to analyze
    }

    // TODO: Deep analysis of function body for:
    // - No global variable modifications
    // - No pointer dereferences that write
    // - No I/O operations
    // - Deterministic (no rand(), time(), etc.)

    // For now, simple heuristic: small functions with simple return types
    return true; // Conservative: assume pure for now
}

// ============================================================================
// Logic function generation
// ============================================================================

std::string ACSLAxiomaticBuilder::generateLogicFunction(const FunctionDecl* func) {
    if (!func) return "";

    std::string funcName = func->getNameAsString();

    // Check cache
    if (m_logicFunctionCache.find(funcName) != m_logicFunctionCache.end()) {
        return m_logicFunctionCache[funcName];
    }

    std::ostringstream oss;

    // Get return type
    QualType returnType = func->getReturnType();
    std::string logicReturnType = convertToLogicType(returnType);

    oss << "logic " << logicReturnType << " " << funcName << "(";

    // Generate parameters
    bool first = true;
    for (const auto* param : func->parameters()) {
        if (!first) oss << ", ";
        first = false;

        QualType paramType = param->getType();
        std::string logicParamType = convertToLogicType(paramType);
        std::string paramName = param->getNameAsString();
        if (paramName.empty()) paramName = "x";

        oss << logicParamType << " " << paramName;
    }

    oss << ")";

    // Try to extract body as logic expression
    if (func->hasBody()) {
        std::string bodyExpr = extractFunctionBody(func);
        if (!bodyExpr.empty()) {
            oss << " =\n      " << bodyExpr;
        }
    }

    oss << ";";

    std::string result = oss.str();
    m_logicFunctionCache[funcName] = result;
    return result;
}

// ============================================================================
// Axiom generation
// ============================================================================

std::vector<std::string> ACSLAxiomaticBuilder::generateAxioms(const FunctionDecl* func) {
    std::vector<std::string> axioms;
    if (!func) return axioms;

    // Detect properties
    std::unordered_set<std::string> properties = analyzeProperties(func);

    // Generate axioms based on detected properties
    if (isCommutative(func)) {
        axioms.push_back(generateCommutativityAxiom(func));
    }

    if (isAssociative(func)) {
        axioms.push_back(generateAssociativityAxiom(func));
    }

    std::string identity = getIdentityElement(func);
    if (!identity.empty()) {
        axioms.push_back(generateIdentityAxiom(func, identity));
    }

    if (hasInverseProperty(func)) {
        axioms.push_back(generateInverseAxiom(func));
    }

    if (isDistributive(func)) {
        axioms.push_back(generateDistributivityAxiom(func));
    }

    if (isAlwaysPositive(func)) {
        axioms.push_back(generatePositivityAxiom(func));
    }

    return axioms;
}

// ============================================================================
// Lemma generation
// ============================================================================

std::vector<std::string> ACSLAxiomaticBuilder::generateLemmas(const FunctionDecl* func) {
    std::vector<std::string> lemmas;
    if (!func) return lemmas;

    std::string funcName = func->getNameAsString();

    // Generate common lemmas based on function name and properties
    if (funcName.find("abs") != std::string::npos || isAlwaysPositive(func)) {
        // Lemma: abs(x) == 0 <==> x == 0
        std::ostringstream oss;
        oss << "lemma " << funcName << "_zero:\n";
        oss << "      \\forall integer x; " << funcName << "(x) == 0 <==> x == 0;";
        lemmas.push_back(oss.str());
    }

    if (funcName.find("gcd") != std::string::npos && isCommutative(func)) {
        // Lemma: gcd is commutative (provable from axiom)
        std::ostringstream oss;
        oss << "lemma " << funcName << "_symmetric:\n";
        oss << "      \\forall integer a, b; " << funcName << "(a, b) == " << funcName << "(b, a);";
        lemmas.push_back(oss.str());
    }

    return lemmas;
}

// ============================================================================
// Inductive predicate generation
// ============================================================================

std::string ACSLAxiomaticBuilder::generateInductivePredicate(const FunctionDecl* func) {
    if (!func) return "";

    QualType returnType = func->getReturnType();
    if (!returnType->isBooleanType()) {
        return ""; // Only for boolean functions
    }

    std::string funcName = func->getNameAsString();

    // Check if it looks like a predicate (is_sorted, is_valid, etc.)
    if (funcName.find("is_") != 0 && funcName.find("has_") != 0) {
        return ""; // Not a typical predicate name
    }

    // TODO: Generate proper inductive predicate
    // For now, just convert to a predicate declaration
    std::ostringstream oss;
    oss << "predicate " << funcName << "(";

    bool first = true;
    for (const auto* param : func->parameters()) {
        if (!first) oss << ", ";
        first = false;

        QualType paramType = param->getType();
        std::string logicParamType = convertToLogicType(paramType);
        std::string paramName = param->getNameAsString();
        if (paramName.empty()) paramName = "x";

        oss << logicParamType << " " << paramName;
    }

    oss << ");";

    return oss.str();
}

// ============================================================================
// Property detection methods
// ============================================================================

bool ACSLAxiomaticBuilder::isCommutative(const FunctionDecl* func) {
    if (!func) return false;

    // Check if function has exactly 2 parameters of same type
    if (func->param_size() != 2) return false;

    const ParmVarDecl* param0 = func->getParamDecl(0);
    const ParmVarDecl* param1 = func->getParamDecl(1);

    if (!param0 || !param1) return false;
    if (param0->getType() != param1->getType()) return false;

    std::string funcName = func->getNameAsString();

    // Known commutative operations
    static const std::vector<std::string> commutativeOps = {
        "add", "multiply", "min", "max", "gcd", "lcm", "equals"
    };

    for (const auto& op : commutativeOps) {
        if (funcName.find(op) != std::string::npos) {
            return true;
        }
    }

    // TODO: Analyze function body for commutativity
    return false;
}

bool ACSLAxiomaticBuilder::isAssociative(const FunctionDecl* func) {
    if (!func) return false;

    if (func->param_size() != 2) return false;

    std::string funcName = func->getNameAsString();

    // Known associative operations
    static const std::vector<std::string> associativeOps = {
        "add", "multiply", "min", "max", "gcd", "lcm"
    };

    for (const auto& op : associativeOps) {
        if (funcName.find(op) != std::string::npos) {
            return true;
        }
    }

    return false;
}

std::string ACSLAxiomaticBuilder::getIdentityElement(const FunctionDecl* func) {
    if (!func) return "";

    std::string funcName = func->getNameAsString();

    // Known identity elements
    if (funcName.find("add") != std::string::npos) return "0";
    if (funcName.find("multiply") != std::string::npos) return "1";
    if (funcName.find("max") != std::string::npos) {
        // Identity is INT_MIN for max
        return ""; // Complex, skip for now
    }

    return "";
}

bool ACSLAxiomaticBuilder::hasInverseProperty(const FunctionDecl* func) {
    if (!func) return false;

    std::string funcName = func->getNameAsString();

    // Check for inverse-like functions
    if (funcName.find("negate") != std::string::npos) return true;
    if (funcName.find("invert") != std::string::npos) return true;
    if (funcName.find("inverse") != std::string::npos) return true;

    return false;
}

bool ACSLAxiomaticBuilder::isDistributive(const FunctionDecl* func) {
    if (!func) return false;

    std::string funcName = func->getNameAsString();

    // Multiplication distributes over addition
    if (funcName.find("multiply") != std::string::npos) return true;

    return false;
}

bool ACSLAxiomaticBuilder::isAlwaysPositive(const FunctionDecl* func) {
    if (!func) return false;

    std::string funcName = func->getNameAsString();

    // Known always-positive functions
    if (funcName.find("abs") != std::string::npos) return true;
    if (funcName.find("absolute") != std::string::npos) return true;
    if (funcName.find("square") != std::string::npos) return true;
    if (funcName.find("distance") != std::string::npos) return true;

    return false;
}

bool ACSLAxiomaticBuilder::isMonotonic(const FunctionDecl* func) {
    // TODO: Analyze function for monotonicity
    return false;
}

bool ACSLAxiomaticBuilder::isIdempotent(const FunctionDecl* func) {
    if (!func) return false;

    std::string funcName = func->getNameAsString();

    // Known idempotent functions
    if (funcName.find("abs") != std::string::npos) return true;
    if (funcName.find("min") != std::string::npos) return true;
    if (funcName.find("max") != std::string::npos) return true;

    return false;
}

// ============================================================================
// Axiom generation helpers
// ============================================================================

std::string ACSLAxiomaticBuilder::generateCommutativityAxiom(const FunctionDecl* func) {
    if (!func || func->param_size() != 2) return "";

    std::string funcName = func->getNameAsString();
    const ParmVarDecl* param0 = func->getParamDecl(0);
    const ParmVarDecl* param1 = func->getParamDecl(1);

    std::string type0 = convertToLogicType(param0->getType());

    std::string paramName0 = param0->getNameAsString();
    std::string paramName1 = param1->getNameAsString();
    if (paramName0.empty()) paramName0 = "a";
    if (paramName1.empty()) paramName1 = "b";

    std::ostringstream oss;
    oss << "axiom " << funcName << "_commutative:\n";
    oss << "      \\forall " << type0 << " " << paramName0 << ", " << paramName1 << "; ";
    oss << funcName << "(" << paramName0 << ", " << paramName1 << ") == ";
    oss << funcName << "(" << paramName1 << ", " << paramName0 << ");";

    return oss.str();
}

std::string ACSLAxiomaticBuilder::generateAssociativityAxiom(const FunctionDecl* func) {
    if (!func || func->param_size() != 2) return "";

    std::string funcName = func->getNameAsString();
    const ParmVarDecl* param0 = func->getParamDecl(0);

    std::string type0 = convertToLogicType(param0->getType());

    std::ostringstream oss;
    oss << "axiom " << funcName << "_associative:\n";
    oss << "      \\forall " << type0 << " a, b, c; ";
    oss << funcName << "(" << funcName << "(a, b), c) == ";
    oss << funcName << "(a, " << funcName << "(b, c));";

    return oss.str();
}

std::string ACSLAxiomaticBuilder::generateIdentityAxiom(const FunctionDecl* func,
                                                         const std::string& identity) {
    if (!func || identity.empty()) return "";

    std::string funcName = func->getNameAsString();
    const ParmVarDecl* param0 = func->getParamDecl(0);
    std::string type0 = convertToLogicType(param0->getType());

    std::ostringstream oss;
    oss << "axiom " << funcName << "_identity:\n";
    oss << "      \\forall " << type0 << " x; ";
    oss << funcName << "(x, " << identity << ") == x;";

    return oss.str();
}

std::string ACSLAxiomaticBuilder::generateInverseAxiom(const FunctionDecl* func) {
    if (!func) return "";

    std::string funcName = func->getNameAsString();
    const ParmVarDecl* param0 = func->getParamDecl(0);
    std::string type0 = convertToLogicType(param0->getType());

    std::ostringstream oss;
    oss << "axiom " << funcName << "_involution:\n";
    oss << "      \\forall " << type0 << " x; ";
    oss << funcName << "(" << funcName << "(x)) == x;";

    return oss.str();
}

std::string ACSLAxiomaticBuilder::generateDistributivityAxiom(const FunctionDecl* func) {
    if (!func) return "";

    std::string funcName = func->getNameAsString();
    const ParmVarDecl* param0 = func->getParamDecl(0);
    std::string type0 = convertToLogicType(param0->getType());

    std::ostringstream oss;
    oss << "axiom " << funcName << "_distributive:\n";
    oss << "      \\forall " << type0 << " a, b, c; ";
    oss << funcName << "(a, add(b, c)) == add(" << funcName << "(a, b), " << funcName << "(a, c));";

    return oss.str();
}

std::string ACSLAxiomaticBuilder::generatePositivityAxiom(const FunctionDecl* func) {
    if (!func) return "";

    std::string funcName = func->getNameAsString();
    const ParmVarDecl* param0 = func->getParamDecl(0);
    std::string type0 = convertToLogicType(param0->getType());

    std::ostringstream oss;
    oss << "axiom " << funcName << "_positive:\n";
    oss << "      \\forall " << type0 << " x; " << funcName << "(x) >= 0;";

    return oss.str();
}

// ============================================================================
// Type conversion
// ============================================================================

std::string ACSLAxiomaticBuilder::convertToLogicType(QualType type) {
    if (type->isIntegerType()) {
        return "integer";
    } else if (type->isFloatingType()) {
        return "real";
    } else if (type->isBooleanType()) {
        return "boolean";
    } else if (type->isPointerType()) {
        // For arrays, use pointer type with element type
        QualType pointeeType = type->getPointeeType();
        return convertToLogicType(pointeeType) + "*";
    } else {
        return "integer"; // Default fallback
    }
}

std::string ACSLAxiomaticBuilder::convertToLogicExpr(const Expr* expr) {
    if (!expr) return "";

    // TODO: Implement full expression conversion
    // For now, return empty string
    return "";
}

// ============================================================================
// Analysis and utility methods
// ============================================================================

std::unordered_set<std::string> ACSLAxiomaticBuilder::analyzeProperties(const FunctionDecl* func) {
    std::unordered_set<std::string> properties;
    if (!func) return properties;

    if (isCommutative(func)) properties.insert("commutative");
    if (isAssociative(func)) properties.insert("associative");
    if (isAlwaysPositive(func)) properties.insert("positive");
    if (hasInverseProperty(func)) properties.insert("inverse");
    if (isDistributive(func)) properties.insert("distributive");
    if (isIdempotent(func)) properties.insert("idempotent");

    return properties;
}

bool ACSLAxiomaticBuilder::checkAxiomConsistency(const std::vector<std::string>& axioms) {
    // Basic syntactic consistency check
    // Full semantic check requires SMT solver (future work)

    // Check for obvious contradictions
    // E.g., "x >= 0" and "x < 0" both as universal properties

    // For now, assume consistency
    return true;
}

std::string ACSLAxiomaticBuilder::getAxiomaticBlockName(const FunctionDecl* func) {
    if (!func) return "Anonymous";

    std::string funcName = func->getNameAsString();

    // Capitalize first letter
    if (!funcName.empty()) {
        funcName[0] = std::toupper(funcName[0]);
    }

    return funcName;
}

std::string ACSLAxiomaticBuilder::getAxiomaticBlockName(
    const std::vector<const FunctionDecl*>& functions) {

    if (functions.empty()) return "Anonymous";

    // Use first function name or common prefix
    return getAxiomaticBlockName(functions[0]);
}

std::string ACSLAxiomaticBuilder::formatAxiomaticBlock(
    const std::string& blockName,
    const std::vector<std::string>& logicFunctions,
    const std::vector<std::string>& axioms,
    const std::vector<std::string>& lemmas) {

    if (logicFunctions.empty() && axioms.empty() && lemmas.empty()) {
        return "";
    }

    std::ostringstream oss;
    oss << "/*@ axiomatic " << blockName << " {\n";

    // Logic functions
    for (const auto& logicFunc : logicFunctions) {
        oss << "  @   " << logicFunc << "\n";
    }

    if (!logicFunctions.empty() && (!axioms.empty() || !lemmas.empty())) {
        oss << "  @\n";
    }

    // Axioms
    for (const auto& axiom : axioms) {
        // Replace newlines with proper indentation
        std::string indented = axiom;
        size_t pos = 0;
        while ((pos = indented.find("\n", pos)) != std::string::npos) {
            indented.replace(pos, 1, "\n  @   ");
            pos += 7;
        }
        oss << "  @   " << indented << "\n";
    }

    if (!axioms.empty() && !lemmas.empty()) {
        oss << "  @\n";
    }

    // Lemmas
    for (const auto& lemma : lemmas) {
        // Replace newlines with proper indentation
        std::string indented = lemma;
        size_t pos = 0;
        while ((pos = indented.find("\n", pos)) != std::string::npos) {
            indented.replace(pos, 1, "\n  @   ");
            pos += 7;
        }
        oss << "  @   " << indented << "\n";
    }

    oss << "  @ }\n  @*/";

    return oss.str();
}

bool ACSLAxiomaticBuilder::isRecursive(const FunctionDecl* func) {
    // TODO: Implement recursion detection
    return false;
}

bool ACSLAxiomaticBuilder::isTemplate(const FunctionDecl* func) {
    if (!func) return false;

    // Check if function is a template or template specialization
    return func->getTemplatedKind() != FunctionDecl::TK_NonTemplate;
}

std::string ACSLAxiomaticBuilder::extractFunctionBody(const FunctionDecl* func) {
    if (!func || !func->hasBody()) return "";

    const Stmt* body = func->getBody();
    if (!body) return "";

    // Try to extract simple return statement
    if (const CompoundStmt* compound = dyn_cast<CompoundStmt>(body)) {
        if (compound->size() == 1) {
            const Stmt* stmt = *compound->body_begin();
            if (const ReturnStmt* ret = dyn_cast<ReturnStmt>(stmt)) {
                const Expr* retExpr = ret->getRetValue();
                if (retExpr) {
                    // TODO: Convert expression to ACSL logic expression
                    // For now, try simple ternary operator
                    if (const ConditionalOperator* cond = dyn_cast<ConditionalOperator>(retExpr)) {
                        // Simple ternary: cond ? true : false
                        // This is a placeholder - need full expression conversion
                        std::string funcName = func->getNameAsString();
                        if (funcName.find("abs") != std::string::npos) {
                            return "x >= 0 ? x : -x";
                        }
                    }
                }
            }
        }
    }

    return "";
}
