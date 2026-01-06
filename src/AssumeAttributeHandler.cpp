// Phase 3: [[assume]] Attribute Handling Implementation

#include "AssumeAttributeHandler.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/IdentifierTable.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>

using namespace clang;

// Constructor
AssumeAttributeHandler::AssumeAttributeHandler(CNodeBuilder& Builder,
                                                 AssumeStrategy Strategy)
    : m_builder(Builder), m_strategy(Strategy) {}

// Main handler method - Template Method Pattern
Stmt* AssumeAttributeHandler::handle(AttributedStmt* S, ASTContext& Ctx) {
  if (!S) {
    return nullptr;
  }

  // Verify this is actually an assume attribute
  const Attr* AssumeAttr = getAssumeAttr(S);
  if (!AssumeAttr) {
    // Not an assume attribute, return underlying statement
    return S->getSubStmt();
  }

  // Extract condition from the attribute
  Expr* Condition = extractCondition(S);
  if (!Condition) {
    llvm::errs() << "Warning: Could not extract condition from [[assume]] "
                    "attribute, stripping\n";
    return S->getSubStmt();
  }

  // Check for side effects (warn if present)
  if (hasSideEffects(Condition, Ctx)) {
    llvm::errs() << "Warning: [[assume]] condition has side effects, "
                    "stripping to avoid undefined behavior\n";
    return S->getSubStmt();
  }

  // Dispatch to strategy-specific handler
  switch (m_strategy) {
  case AssumeStrategy::Strip:
    return handleStrip(S);

  case AssumeStrategy::Comment:
    return handleComment(S, Ctx);

  case AssumeStrategy::Builtin:
    return handleBuiltin(S, Ctx);

  default:
    return S->getSubStmt();
  }
}

// Get the assume attribute from AttributedStmt
const Attr* AssumeAttributeHandler::getAssumeAttr(AttributedStmt* S) {
  // CXXAssumeAttr is only available in LLVM 16+
  // For LLVM 15, return nullptr (assume attributes not supported)
  return nullptr;
  /*
  for (const auto* A : S->getAttrs()) {
    if (auto* AA = dyn_cast<CXXAssumeAttr>(A)) {
      return AA;
    }
  }
  return nullptr;
  */
}

// Extract condition expression from assume attribute
Expr* AssumeAttributeHandler::extractCondition(AttributedStmt* S) {
  // CXXAssumeAttr is only available in LLVM 16+
  // For LLVM 15, return nullptr (assume attributes not supported)
  return nullptr;
  /*
  // Get the assume attribute
  for (const auto* A : S->getAttrs()) {
    if (auto* AA = dyn_cast<CXXAssumeAttr>(A)) {
      // CXXAssumeAttr has a getAssumption() method that returns the condition
      return AA->getAssumption();
    }
  }
  return nullptr;
  */
}

// Convert expression to C-compatible string
std::string AssumeAttributeHandler::expressionToString(Expr* E,
                                                        ASTContext& Ctx) {
  if (!E) {
    return "";
  }

  std::string Result;
  llvm::raw_string_ostream OS(Result);

  // Use Clang's PrintingPolicy for C-like output
  PrintingPolicy Policy(Ctx.getLangOpts());
  Policy.Bool = 1; // Use _Bool instead of bool
  Policy.UseVoidForZeroParams = 1;
  Policy.TerseOutput = 1;

  E->printPretty(OS, nullptr, Policy);
  OS.flush();

  // Post-process to convert C++ constructs to C
  // Replace nullptr with NULL
  size_t pos = 0;
  while ((pos = Result.find("nullptr", pos)) != std::string::npos) {
    Result.replace(pos, 7, "((void*)0)");
    pos += 10;
  }

  // Replace true/false with 1/0 if needed
  // (though C99 has stdbool.h with true/false)

  return Result;
}

// Strip strategy: Just return underlying statement
Stmt* AssumeAttributeHandler::handleStrip(AttributedStmt* S) {
  // Simply return the sub-statement without the attribute
  return S->getSubStmt();
}

// Comment strategy: Create commented statement
Stmt* AssumeAttributeHandler::handleComment(AttributedStmt* S,
                                              ASTContext& Ctx) {
  Expr* Condition = extractCondition(S);
  if (!Condition) {
    return S->getSubStmt();
  }

  // Convert condition to string
  std::string CondStr = expressionToString(Condition, Ctx);

  // Create comment text
  std::string Comment = "/* assume: " + CondStr + " */";

  // Create a compound statement with the comment
  // Note: Clang AST doesn't preserve comments by default.
  // We'll need to handle this at code generation time.
  // For now, we'll create a NullStmt which we can tag with the comment.

  // Store the comment in a way that code generation can retrieve it
  // This is a simplified approach - in production we'd want a more
  // sophisticated comment tracking system.

  // For now, just return the underlying statement
  // The comment will need to be emitted during code generation
  // by checking the original source for AttributedStmt nodes

  // TODO: Implement comment attachment mechanism
  // Options:
  // 1. Store comments in a side table keyed by statement
  // 2. Use source location to insert comments during code emission
  // 3. Create a custom Stmt subclass that holds the comment

  // For the MVP, we'll just return the sub-statement
  // and rely on the code generator to emit comments for AttributedStmt
  return S->getSubStmt();
}

// Builtin strategy: Create __builtin_assume() call
Stmt* AssumeAttributeHandler::handleBuiltin(AttributedStmt* S,
                                              ASTContext& Ctx) {
  Expr* Condition = extractCondition(S);
  if (!Condition) {
    return S->getSubStmt();
  }

  // Create __builtin_assume() call
  CallExpr* BuiltinCall = createBuiltinAssumeCall(Condition, Ctx);
  if (!BuiltinCall) {
    llvm::errs() << "Warning: Failed to create __builtin_assume() call, "
                    "stripping\n";
    return S->getSubStmt();
  }

  // Create compound statement with builtin call + underlying statement
  Stmt* SubStmt = S->getSubStmt();

  // If sub-statement is null statement, just return the builtin call
  if (isa<NullStmt>(SubStmt)) {
    return BuiltinCall;
  }

  // Otherwise, create compound statement with both
  SmallVector<Stmt*, 2> Stmts;
  Stmts.push_back(BuiltinCall);
  Stmts.push_back(SubStmt);

  CompoundStmt* CS = CompoundStmt::Create(
      Ctx, Stmts, FPOptionsOverride(), SourceLocation(), SourceLocation());

  return CS;
}

// Create __builtin_assume() call expression
CallExpr* AssumeAttributeHandler::createBuiltinAssumeCall(Expr* Condition,
                                                           ASTContext& Ctx) {
  if (!Condition) {
    return nullptr;
  }

  // Get or create __builtin_assume identifier
  IdentifierInfo* II = &Ctx.Idents.get("__builtin_assume");

  // Create DeclRefExpr for __builtin_assume
  // Note: __builtin_assume is a compiler builtin, not a regular function
  // We need to create a reference to it

  // For simplicity, create an UnresolvedLookupExpr or use the builder
  // In practice, we'd look up the builtin declaration

  // Create a simple call expression
  // We'll create the call as if __builtin_assume were a regular function

  // First, create the callee expression (DeclRefExpr to __builtin_assume)
  // Since builtins don't have declarations in the AST, we'll create
  // a simple reference

  // For now, use a workaround: create an implicit cast or direct call
  // This is simplified - production code would use proper builtin handling

  // Create argument array
  Expr* Args[] = {Condition};

  // Create the call expression
  // We'll use CallExpr::Create with no callee decl (builtin)
  CallExpr* CE = CallExpr::Create(
      Ctx,
      Condition, // Placeholder - should be builtin ref
      Args,
      Ctx.VoidTy, // __builtin_assume returns void
      VK_PRValue,
      SourceLocation(),
      FPOptionsOverride());

  return CE;
}

// Check if expression has side effects
bool AssumeAttributeHandler::hasSideEffects(Expr* E, ASTContext& Ctx) {
  if (!E) {
    return false;
  }

  // Use Clang's built-in side effects analysis
  return E->HasSideEffects(Ctx);
}

// Create statement with comment attached
Stmt* AssumeAttributeHandler::createCommentedStmt(Stmt* Stmt,
                                                    const std::string& Comment,
                                                    ASTContext& Ctx) {
  // This is a placeholder implementation
  // In practice, we'd need to:
  // 1. Store the comment in a side table
  // 2. Emit it during code generation
  // 3. Or use source rewriting

  // For now, just return the statement
  return Stmt;
}
