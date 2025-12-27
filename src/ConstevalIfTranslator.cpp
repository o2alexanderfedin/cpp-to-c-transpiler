#include "ConstevalIfTranslator.h"
#include "clang/AST/ParentMapContext.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;

ConstevalIfTranslator::ConstevalIfTranslator(CNodeBuilder& Builder,
                                            ConstevalStrategy Strategy)
    : m_builder(Builder), m_strategy(Strategy) {}

Stmt* ConstevalIfTranslator::transform(IfStmt* S, ASTContext& Ctx) {
    if (!S) {
        return nullptr;
    }

    // Get branches
    Stmt* ThenBranch = S->getThen();    // consteval path (compile-time)
    Stmt* ElseBranch = S->getElse();    // runtime path

    // Check for negated form: if !consteval or if not consteval
    bool IsNegated = S->isNegatedConsteval();

    // If negated, swap branches:
    // "if !consteval { A } else { B }" means:
    //   - A is runtime path
    //   - B is compile-time path
    if (IsNegated) {
        std::swap(ThenBranch, ElseBranch);
    }

    // Now:
    // - ThenBranch = compile-time path
    // - ElseBranch = runtime path

    // Select branch based on strategy
    Stmt* SelectedBranch = nullptr;

    switch (m_strategy) {
        case ConstevalStrategy::Runtime:
            // Always use runtime (else) branch - conservative approach
            SelectedBranch = ElseBranch;
            emitWarning("if consteval: using runtime path (C has no consteval)", S, Ctx);
            break;

        case ConstevalStrategy::Optimistic:
            // Try to detect compile-time context
            {
                bool IsConstexprContext = analyzeContext(S, Ctx);
                if (IsConstexprContext) {
                    SelectedBranch = ThenBranch;
                    emitWarning("if consteval: using compile-time path", S, Ctx);
                } else {
                    SelectedBranch = ElseBranch;
                    emitWarning("if consteval: using runtime path", S, Ctx);
                }
            }
            break;

        case ConstevalStrategy::Both:
            // Future: Emit both paths with #ifdef (complex, deferred)
            // For now, fall back to runtime
            SelectedBranch = ElseBranch;
            emitWarning("if consteval: Both strategy not implemented, using runtime path", S, Ctx);
            break;
    }

    // If no selected branch (e.g., no else and we selected runtime), return nullptr
    if (!SelectedBranch) {
        // No runtime branch available - emit warning and return nullptr
        emitWarning("if consteval: no runtime branch available, statement removed", S, Ctx);
        return nullptr;
    }

    return SelectedBranch;
}

bool ConstevalIfTranslator::analyzeContext(IfStmt* S, ASTContext& Ctx) {
    // Find enclosing function
    FunctionDecl* EnclosingFunc = findEnclosingFunction(S, Ctx);
    if (!EnclosingFunc) {
        return false;  // Not in function → runtime
    }

    // If function is not constexpr, definitely runtime
    if (!EnclosingFunc->isConstexpr()) {
        return false;
    }

    // Conservative: Even in constexpr function, default to runtime
    // Reason: A constexpr function can be called at runtime OR compile-time
    // We would need whole-program analysis to determine which
    // For now: always assume runtime (safe, conservative)

    // Future enhancement: Track call sites to determine if called in constexpr context
    // This requires analyzing:
    // 1. Variable initializers (constexpr int x = func())
    // 2. Template arguments
    // 3. static_assert arguments
    // 4. Other constexpr function calls

    return false;  // Conservative approach
}

FunctionDecl* ConstevalIfTranslator::findEnclosingFunction(IfStmt* S, ASTContext& Ctx) {
    // Use ParentMapContext to traverse up the AST
    auto& Parents = Ctx.getParentMapContext();

    DynTypedNode Node = DynTypedNode::create(*S);

    while (true) {
        auto ParentNodes = Parents.getParents(Node);
        if (ParentNodes.empty()) {
            break;
        }

        Node = ParentNodes[0];

        // Check if this node is a FunctionDecl
        if (auto* FD = Node.get<FunctionDecl>()) {
            return const_cast<FunctionDecl*>(FD);
        }
    }

    return nullptr;
}

bool ConstevalIfTranslator::isDefinitelyConstexprContext(IfStmt* S,
                                                         FunctionDecl* Func,
                                                         ASTContext& Ctx) {
    // This is a placeholder for future enhancement
    // Currently always returns false (conservative)

    // To implement properly, we would need to:
    // 1. Check if Func is called from constexpr contexts
    // 2. Check if we're in a constexpr variable initializer
    // 3. Check if we're in a template argument
    // 4. Check if we're in a static_assert

    return false;
}

void ConstevalIfTranslator::emitWarning(const std::string& message,
                                       IfStmt* S,
                                       ASTContext& Ctx) {
    // Emit diagnostic to stderr
    llvm::errs() << "Warning: " << message
                 << " at " << S->getBeginLoc().printToString(Ctx.getSourceManager())
                 << "\n";
}
