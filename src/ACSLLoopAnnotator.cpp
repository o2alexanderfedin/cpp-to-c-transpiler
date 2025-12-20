// Epic #193: ACSL Annotation Generation for Transpiled Code
// Story #197: Implement ACSLLoopAnnotator for comprehensive loop annotations
//
// Implementation following TDD and SOLID principles:
// - Pattern detection for common loop idioms
// - RecursiveASTVisitor for loop body analysis
// - Incremental complexity: start simple, add patterns over time

#include "ACSLLoopAnnotator.h"
#include "clang/AST/OperationKinds.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <set>
#include <sstream>

using namespace clang;

// Default constructor
ACSLLoopAnnotator::ACSLLoopAnnotator() : ACSLGenerator() {}

// Constructor with ACSL level
ACSLLoopAnnotator::ACSLLoopAnnotator(ACSLLevel level) : ACSLGenerator(level) {}

// Constructor with ACSL level and output mode
ACSLLoopAnnotator::ACSLLoopAnnotator(ACSLLevel level, ACSLOutputMode mode)
    : ACSLGenerator(level, mode) {}

// Generate loop annotations for ForStmt
std::string ACSLLoopAnnotator::generateLoopAnnotations(const ForStmt *loop) {
  if (!loop) {
    return "";
  }

  std::vector<std::string> invariants = generateLoopInvariants(loop);
  std::string variant = generateLoopVariant(loop);
  std::vector<std::string> assigns = generateLoopAssigns(loop);

  // Build complete annotation block
  std::ostringstream oss;

  // Add loop invariants
  for (const auto &inv : invariants) {
    oss << "loop invariant " << inv << ";\n";
  }

  // Add loop variant (if available)
  if (!variant.empty()) {
    oss << "loop variant " << variant << ";\n";
  }

  // Add loop assigns
  if (!assigns.empty()) {
    oss << "loop assigns " << formatLoopAssignsClause(assigns) << ";\n";
  }

  std::string annotation = oss.str();
  if (!annotation.empty() && annotation.back() == '\n') {
    annotation.pop_back(); // Remove trailing newline for formatting
  }

  return formatACSLComment(annotation);
}

// Generate loop annotations for WhileStmt
std::string ACSLLoopAnnotator::generateLoopAnnotations(const WhileStmt *loop) {
  if (!loop) {
    return "";
  }

  std::vector<std::string> invariants = generateLoopInvariants(loop);
  std::string variant = generateLoopVariant(loop);
  std::vector<std::string> assigns = generateLoopAssigns(loop);

  // Build complete annotation block
  std::ostringstream oss;

  // Add loop invariants
  for (const auto &inv : invariants) {
    oss << "loop invariant " << inv << ";\n";
  }

  // Add loop variant (if available)
  if (!variant.empty()) {
    oss << "loop variant " << variant << ";\n";
  }

  // Add loop assigns
  if (!assigns.empty()) {
    oss << "loop assigns " << formatLoopAssignsClause(assigns) << ";\n";
  }

  std::string annotation = oss.str();
  if (!annotation.empty() && annotation.back() == '\n') {
    annotation.pop_back(); // Remove trailing newline
  }

  return formatACSLComment(annotation);
}

// Generate loop annotations for DoStmt
std::string ACSLLoopAnnotator::generateLoopAnnotations(const DoStmt *loop) {
  if (!loop) {
    return "";
  }

  std::vector<std::string> invariants = generateLoopInvariants(loop);
  std::string variant = generateLoopVariant(loop);
  std::vector<std::string> assigns = generateLoopAssigns(loop);

  // Build complete annotation block
  std::ostringstream oss;

  // Add loop invariants
  for (const auto &inv : invariants) {
    oss << "loop invariant " << inv << ";\n";
  }

  // Add loop variant (if available)
  if (!variant.empty()) {
    oss << "loop variant " << variant << ";\n";
  }

  // Add loop assigns
  if (!assigns.empty()) {
    oss << "loop assigns " << formatLoopAssignsClause(assigns) << ";\n";
  }

  std::string annotation = oss.str();
  if (!annotation.empty() && annotation.back() == '\n') {
    annotation.pop_back(); // Remove trailing newline
  }

  return formatACSLComment(annotation);
}

// Helper visitor class to collect variable modifications
class LoopModificationVisitor
    : public RecursiveASTVisitor<LoopModificationVisitor> {
public:
  std::set<std::string> modifiedVars;
  std::set<std::string> arrayAccesses;

  bool VisitBinaryOperator(BinaryOperator *binOp) {
    if (binOp->isAssignmentOp()) {
      // Track left-hand side of assignment
      Expr *lhs = binOp->getLHS();
      if (auto *declRef = dyn_cast<DeclRefExpr>(lhs->IgnoreImpCasts())) {
        modifiedVars.insert(declRef->getNameInfo().getAsString());
      } else if (auto *arrayExpr =
                     dyn_cast<ArraySubscriptExpr>(lhs->IgnoreImpCasts())) {
        // Track array base name
        if (auto *base =
                dyn_cast<DeclRefExpr>(arrayExpr->getBase()->IgnoreImpCasts())) {
          std::string arrayName = base->getNameInfo().getAsString();
          arrayAccesses.insert(arrayName);
        }
      }
    }
    return true;
  }

  bool VisitUnaryOperator(UnaryOperator *unaryOp) {
    // Track ++ and -- operators
    if (unaryOp->isIncrementDecrementOp()) {
      if (auto *declRef =
              dyn_cast<DeclRefExpr>(unaryOp->getSubExpr()->IgnoreImpCasts())) {
        modifiedVars.insert(declRef->getNameInfo().getAsString());
      }
    }
    return true;
  }
};

// Generate loop invariants
std::vector<std::string>
ACSLLoopAnnotator::generateLoopInvariants(const Stmt *loop) {
  std::vector<std::string> invariants;

  if (!loop) {
    return invariants;
  }

  // Detect loop counter and bounds for all loop types
  std::string counter;
  auto bounds = detectLoopBounds(loop);

  // For ForStmt, use dedicated counter detection
  if (auto *forLoop = dyn_cast<ForStmt>(loop)) {
    counter = detectLoopCounter(forLoop);
  } else {
    // For while/do-while, extract counter from condition
    counter = extractCounterFromCondition(loop);
  }

  if (!counter.empty()) {
    // Generate bounds invariant: lower_bound <= counter <= upper_bound
    std::ostringstream oss;
    if (!bounds.first.empty() && !bounds.second.empty()) {
      oss << bounds.first << " <= " << counter << " && " << counter
          << " <= " << bounds.second;
    } else if (!bounds.first.empty()) {
      oss << bounds.first << " <= " << counter;
    } else if (!bounds.second.empty()) {
      oss << counter << " <= " << bounds.second;
    }

    if (!oss.str().empty()) {
      invariants.push_back(oss.str());
    }
  }

  // Detect array fill pattern
  std::string arrayFill = detectArrayFillPattern(loop);
  if (!arrayFill.empty()) {
    invariants.push_back(arrayFill);
  }

  // Detect accumulator pattern
  std::string accumulator = detectAccumulatorPattern(loop);
  if (!accumulator.empty()) {
    invariants.push_back(accumulator);
  }

  // Detect array search pattern
  std::string search = detectArraySearchPattern(loop);
  if (!search.empty()) {
    invariants.push_back(search);
  }

  // If no specific patterns detected, generate basic invariant
  if (invariants.empty()) {
    if (auto *forLoop = dyn_cast<ForStmt>(loop)) {
      std::string counter = detectLoopCounter(forLoop);
      if (!counter.empty()) {
        auto bounds = detectLoopBounds(loop);
        if (!bounds.first.empty() || !bounds.second.empty()) {
          std::ostringstream oss;
          oss << bounds.first << " <= " << counter;
          invariants.push_back(oss.str());
        }
      }
    }
  }

  return invariants;
}

// Generate loop variant (termination measure)
std::string ACSLLoopAnnotator::generateLoopVariant(const Stmt *loop) {
  if (!loop) {
    return "";
  }

  std::string counter;
  auto bounds = detectLoopBounds(loop);

  // Detect counter for different loop types
  if (auto *forLoop = dyn_cast<ForStmt>(loop)) {
    counter = detectLoopCounter(forLoop);
  } else {
    // For while/do-while, extract from condition
    counter = extractCounterFromCondition(loop);
  }

  if (!counter.empty()) {
    // For descending loops (i--, i > 0)
    if (isDescendingLoop(loop)) {
      // Variant is simply the counter value (decreases to 0 or lower bound)
      if (!bounds.first.empty() && bounds.first != "0") {
        return counter + " - " + bounds.first;
      }
      return counter;
    }
    // For ascending loops (i++, i < n)
    else if (!bounds.second.empty()) {
      // Variant is upper_bound - counter
      return bounds.second + " - " + counter;
    }
  }

  return "";
}

// Generate loop assigns clause
std::vector<std::string>
ACSLLoopAnnotator::generateLoopAssigns(const Stmt *loop) {
  std::vector<std::string> assigns;

  if (!loop) {
    return assigns;
  }

  // Use visitor to track modifications
  const Stmt *body = getLoopBody(loop);
  if (!body) {
    return assigns;
  }

  LoopModificationVisitor visitor;
  visitor.TraverseStmt(const_cast<Stmt *>(body));

  // Add modified variables
  for (const auto &var : visitor.modifiedVars) {
    assigns.push_back(var);
  }

  // Add array accesses (with range notation)
  for (const auto &arr : visitor.arrayAccesses) {
    // Simple array range notation: arr[..]
    assigns.push_back(arr + "[..]");
  }

  return assigns;
}

// Detect loop counter from ForStmt init
std::string ACSLLoopAnnotator::detectLoopCounter(const ForStmt *loop) {
  if (!loop) {
    return "";
  }

  // Check init statement for variable declaration
  if (const Stmt *init = loop->getInit()) {
    if (auto *declStmt = dyn_cast<DeclStmt>(init)) {
      if (declStmt->isSingleDecl()) {
        if (auto *varDecl = dyn_cast<VarDecl>(declStmt->getSingleDecl())) {
          return varDecl->getNameAsString();
        }
      }
    }
  }

  // Check increment for variable reference
  if (const Expr *inc = loop->getInc()) {
    if (auto *unaryOp = dyn_cast<UnaryOperator>(inc->IgnoreImpCasts())) {
      if (auto *declRef =
              dyn_cast<DeclRefExpr>(unaryOp->getSubExpr()->IgnoreImpCasts())) {
        return declRef->getNameInfo().getAsString();
      }
    }
  }

  return "";
}

// Detect loop bounds from condition
std::pair<std::string, std::string>
ACSLLoopAnnotator::detectLoopBounds(const Stmt *loop) {
  std::pair<std::string, std::string> bounds("0", "");

  const Expr *cond = getLoopCondition(loop);
  if (!cond) {
    return bounds;
  }

  // Parse binary operator condition (e.g., i < n, i <= max)
  if (auto *binOp = dyn_cast<BinaryOperator>(cond->IgnoreImpCasts())) {
    BinaryOperatorKind op = binOp->getOpcode();
    Expr *lhs = binOp->getLHS();
    Expr *rhs = binOp->getRHS();

    std::string lhsStr, rhsStr;

    // Get left side
    if (auto *declRef = dyn_cast<DeclRefExpr>(lhs->IgnoreImpCasts())) {
      lhsStr = declRef->getNameInfo().getAsString();
    }

    // Get right side
    if (auto *declRefR = dyn_cast<DeclRefExpr>(rhs->IgnoreImpCasts())) {
      rhsStr = declRefR->getNameInfo().getAsString();
    } else if (auto *intLit = dyn_cast<IntegerLiteral>(rhs->IgnoreImpCasts())) {
      rhsStr = std::to_string(intLit->getValue().getLimitedValue());
    }

    // Determine bounds based on operator
    if (op == BO_LT || op == BO_LE) {
      // i < n or i <= n
      bounds.second = rhsStr;
    } else if (op == BO_GT || op == BO_GE) {
      // i > 0 or i >= 0
      bounds.first = rhsStr;
    }
  }

  return bounds;
}

// Detect array fill pattern: arr[i] = value
std::string ACSLLoopAnnotator::detectArrayFillPattern(const Stmt *loop) {
  const Stmt *body = getLoopBody(loop);
  if (!body) {
    return "";
  }

  // Look for pattern: arr[i] = constant_or_variable
  // This is a simplified detection - full implementation would use AST visitor
  // For now, return a template invariant for array modifications
  LoopModificationVisitor visitor;
  visitor.TraverseStmt(const_cast<Stmt *>(body));

  if (!visitor.arrayAccesses.empty()) {
    // Get first array and loop counter
    std::string arrayName = *visitor.arrayAccesses.begin();
    std::string counter = "i"; // Default counter name

    if (auto *forLoop = dyn_cast<ForStmt>(loop)) {
      std::string detectedCounter = detectLoopCounter(forLoop);
      if (!detectedCounter.empty()) {
        counter = detectedCounter;
      }
    }

    // Generate quantified invariant
    std::ostringstream oss;
    oss << "\\forall integer j; 0 <= j < " << counter << " ==> " << arrayName
        << "[j] == " << arrayName << "[j]";
    return oss.str();
  }

  return "";
}

// Detect accumulator pattern: sum += expr
std::string ACSLLoopAnnotator::detectAccumulatorPattern(const Stmt *loop) {
  // Simplified implementation - would need more sophisticated analysis
  // to detect actual accumulator patterns
  return "";
}

// Detect array search pattern
std::string ACSLLoopAnnotator::detectArraySearchPattern(const Stmt *loop) {
  // Simplified implementation - would need to detect break statements
  // and search conditions
  return "";
}

// Track loop side effects
std::vector<std::string>
ACSLLoopAnnotator::trackLoopSideEffects(const Stmt *loop) {
  std::vector<std::string> effects;

  const Stmt *body = getLoopBody(loop);
  if (!body) {
    return effects;
  }

  LoopModificationVisitor visitor;
  visitor.TraverseStmt(const_cast<Stmt *>(body));

  for (const auto &var : visitor.modifiedVars) {
    effects.push_back(var);
  }

  for (const auto &arr : visitor.arrayAccesses) {
    effects.push_back(arr);
  }

  return effects;
}

// Check if loop is ascending
bool ACSLLoopAnnotator::isAscendingLoop(const Stmt *loop) {
  if (auto *forLoop = dyn_cast<ForStmt>(loop)) {
    if (const Expr *inc = forLoop->getInc()) {
      if (auto *unaryOp = dyn_cast<UnaryOperator>(inc->IgnoreImpCasts())) {
        return unaryOp->isIncrementOp();
      }
    }
  }
  return true; // Default to ascending
}

// Check if loop is descending
bool ACSLLoopAnnotator::isDescendingLoop(const Stmt *loop) {
  if (auto *forLoop = dyn_cast<ForStmt>(loop)) {
    if (const Expr *inc = forLoop->getInc()) {
      if (auto *unaryOp = dyn_cast<UnaryOperator>(inc->IgnoreImpCasts())) {
        return unaryOp->isDecrementOp();
      }
    }
  }
  return false;
}

// Get loop body
const Stmt *ACSLLoopAnnotator::getLoopBody(const Stmt *loop) {
  if (auto *forLoop = dyn_cast<ForStmt>(loop)) {
    return forLoop->getBody();
  } else if (auto *whileLoop = dyn_cast<WhileStmt>(loop)) {
    return whileLoop->getBody();
  } else if (auto *doLoop = dyn_cast<DoStmt>(loop)) {
    return doLoop->getBody();
  }
  return nullptr;
}

// Get loop condition
const Expr *ACSLLoopAnnotator::getLoopCondition(const Stmt *loop) {
  if (auto *forLoop = dyn_cast<ForStmt>(loop)) {
    return forLoop->getCond();
  } else if (auto *whileLoop = dyn_cast<WhileStmt>(loop)) {
    return whileLoop->getCond();
  } else if (auto *doLoop = dyn_cast<DoStmt>(loop)) {
    return doLoop->getCond();
  }
  return nullptr;
}

// Get loop increment (ForStmt only)
const Expr *ACSLLoopAnnotator::getLoopIncrement(const ForStmt *loop) {
  if (loop) {
    return loop->getInc();
  }
  return nullptr;
}

// Extract counter variable from loop condition (for while/do-while)
std::string ACSLLoopAnnotator::extractCounterFromCondition(const Stmt *loop) {
  const Expr *cond = getLoopCondition(loop);
  if (!cond) {
    return "";
  }

  // Parse binary operator condition (e.g., i < 10, counter < n)
  if (auto *binOp = dyn_cast<BinaryOperator>(cond->IgnoreImpCasts())) {
    Expr *lhs = binOp->getLHS();

    // Get left side variable name (typically the counter)
    if (auto *declRef = dyn_cast<DeclRefExpr>(lhs->IgnoreImpCasts())) {
      return declRef->getNameInfo().getAsString();
    }
  }

  return "";
}

// Format loop assigns clause
std::string ACSLLoopAnnotator::formatLoopAssignsClause(
    const std::vector<std::string> &items) {
  if (items.empty()) {
    return "\\nothing";
  }

  std::ostringstream oss;
  for (size_t i = 0; i < items.size(); ++i) {
    if (i > 0) {
      oss << ", ";
    }
    oss << items[i];
  }
  return oss.str();
}

// Get variable name from expression
std::string ACSLLoopAnnotator::getVariableName(const Expr *expr) {
  if (!expr) {
    return "";
  }

  if (auto *declRef = dyn_cast<DeclRefExpr>(expr->IgnoreImpCasts())) {
    return declRef->getNameInfo().getAsString();
  }

  return "";
}

// Check if expression is array subscript
bool ACSLLoopAnnotator::isArraySubscript(const Expr *expr) {
  if (!expr) {
    return false;
  }
  return isa<ArraySubscriptExpr>(expr->IgnoreImpCasts());
}

// Get array base name
std::string ACSLLoopAnnotator::getArrayBaseName(const Expr *expr) {
  if (!expr) {
    return "";
  }

  if (auto *arrayExpr = dyn_cast<ArraySubscriptExpr>(expr->IgnoreImpCasts())) {
    if (auto *base =
            dyn_cast<DeclRefExpr>(arrayExpr->getBase()->IgnoreImpCasts())) {
      return base->getNameInfo().getAsString();
    }
  }

  return "";
}
