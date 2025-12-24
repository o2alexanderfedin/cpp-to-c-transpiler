#ifndef CONSTEVAL_IF_TRANSLATOR_H
#define CONSTEVAL_IF_TRANSLATOR_H

#include "clang/AST/AST.h"
#include "clang/AST/ASTContext.h"
#include "CNodeBuilder.h"
#include <string>

namespace clang {

// Strategy for handling if consteval statements
// Since C has no compile-time evaluation, we must choose a branch
enum class ConstevalStrategy {
    Runtime,     // Always emit runtime (else) branch (conservative, safe default)
    Optimistic,  // Try to detect compile-time context (future enhancement)
    Both         // Emit both paths with #ifdef (requires preprocessor, future)
};

// Translates C++23 'if consteval' statements to C
//
// C++23 introduces if consteval to differentiate compile-time vs runtime paths:
//   if consteval { compile_time_code(); } else { runtime_code(); }
//
// Since C has no consteval equivalent, we:
// 1. Emit the runtime (else) branch by default (Runtime strategy)
// 2. Emit warnings when optimization is lost
// 3. Handle negation: if !consteval
//
// Single Responsibility: Transform if consteval → C statement
// Open/Closed: Extensible via ConstevalStrategy enum
// Dependency Inversion: Depends on CNodeBuilder abstraction
class ConstevalIfTranslator {
public:
    ConstevalIfTranslator(CNodeBuilder& Builder,
                         ConstevalStrategy Strategy = ConstevalStrategy::Runtime);

    // Transform if consteval → C statement
    // Returns the selected branch statement (runtime by default)
    // Emits warnings when compile-time optimization is lost
    Stmt* transform(IfStmt* S, ASTContext& Ctx);

private:
    CNodeBuilder& m_builder;
    ConstevalStrategy m_strategy;

    // Analyze enclosing context to determine if compile-time or runtime
    // Returns true if definitely compile-time, false otherwise
    bool analyzeContext(IfStmt* S, ASTContext& Ctx);

    // Find the function containing this statement
    FunctionDecl* findEnclosingFunction(IfStmt* S, ASTContext& Ctx);

    // Check if we're definitely in a constexpr context
    // (Conservative: returns false unless proven otherwise)
    bool isDefinitelyConstexprContext(IfStmt* S,
                                     FunctionDecl* Func,
                                     ASTContext& Ctx);

    // Emit a warning/diagnostic message
    void emitWarning(const std::string& message, IfStmt* S, ASTContext& Ctx);
};

} // namespace clang

#endif // CONSTEVAL_IF_TRANSLATOR_H
