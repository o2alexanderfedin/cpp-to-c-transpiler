/**
 * @file NamespaceHandler.cpp
 * @brief Implementation of NamespaceHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle namespace declaration tracking.
 * Computes namespace paths and stores mappings for child handlers to use.
 * Does NOT create C NamespaceDecl (C has no namespaces).
 */

#include "dispatch/NamespaceHandler.h"
#include "mapping/DeclMapper.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/StringRef.h"
#include <cassert>
#include <vector>
#include <algorithm>

namespace cpptoc {

void NamespaceHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &NamespaceHandler::canHandle,
        &NamespaceHandler::handleNamespace
    );
}

bool NamespaceHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // Accept only NamespaceDecl (exact type matching)
    return D->getKind() == clang::Decl::Namespace;
}

void NamespaceHandler::handleNamespace(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(D->getKind() == clang::Decl::Namespace && "Must be NamespaceDecl");

    const auto* cppNamespace = llvm::cast<clang::NamespaceDecl>(D);

    // Check if already processed (avoid duplicates)
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    if (declMapper.hasCreated(cppNamespace)) {
        llvm::outs() << "[NamespaceHandler] Already processed namespace (skipping)\n";
        return;
    }

    // Detect anonymous vs named namespace
    std::string namespaceName;
    bool isAnonymous = cppNamespace->isAnonymousNamespace();

    if (isAnonymous) {
        // Generate unique ID for anonymous namespace
        const clang::SourceManager& SM = cppASTContext.getSourceManager();
        namespaceName = generateAnonymousID(cppNamespace, SM);
        llvm::outs() << "[NamespaceHandler] Anonymous namespace detected → " << namespaceName << "\n";
    } else {
        namespaceName = cppNamespace->getNameAsString();
        llvm::outs() << "[NamespaceHandler] Processing namespace: " << namespaceName << "\n";
    }

    // Compute full namespace path recursively (A::B::C → A_B_C)
    std::string namespacePath = getNamespacePath(cppNamespace);
    llvm::outs() << "[NamespaceHandler] Namespace path: " << namespacePath << "\n";

    // Store namespace mapping for tracking
    // IMPORTANT: C has NO namespaces, so we store nullptr as C value
    // This mapping is for tracking only - child handlers will check parent context
    declMapper.setCreated(cppNamespace, nullptr);

    // Recursively dispatch child declarations
    // Child handlers (FunctionHandler, RecordHandler, etc.) will be updated in Phase 2
    // to check parent context and apply namespace prefix
    processChildDecls(cppNamespace, disp, cppASTContext, cASTContext);

    llvm::outs() << "[NamespaceHandler] Completed processing namespace: " << namespacePath << "\n";
}

std::string NamespaceHandler::getNamespacePath(const clang::NamespaceDecl* NS) {
    std::vector<std::string> parts;

    // Walk parent DeclContexts from inner to outer
    const clang::DeclContext* DC = NS;
    while (DC) {
        if (const auto* nsDecl = llvm::dyn_cast<clang::NamespaceDecl>(DC)) {
            // Skip anonymous namespaces in path computation
            if (!nsDecl->isAnonymousNamespace()) {
                std::string name = nsDecl->getNameAsString();
                if (!name.empty()) {
                    parts.push_back(name);
                }
            }
            DC = DC->getParent();
        } else {
            // Stop when we reach non-namespace context (e.g., TranslationUnit)
            break;
        }
    }

    // Reverse to get outer-to-inner order (A, B, C instead of C, B, A)
    std::reverse(parts.begin(), parts.end());

    // Join with "_" separator
    if (parts.empty()) {
        return "";
    }

    std::string result = parts[0];
    for (size_t i = 1; i < parts.size(); ++i) {
        result += "_" + parts[i];
    }

    return result;
}

std::string NamespaceHandler::generateAnonymousID(
    const clang::NamespaceDecl* NS,
    const clang::SourceManager& SM
) {
    // Get source location
    clang::SourceLocation loc = NS->getLocation();

    // Use raw encoding as deterministic hash
    // This matches the pattern in NameMangler::getAnonymousNamespaceID()
    unsigned hash = loc.getRawEncoding();

    // Generate unique ID: __anon_<hash>
    return "__anon_" + std::to_string(hash);
}

void NamespaceHandler::processChildDecls(
    const clang::NamespaceDecl* NS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext
) {
    // Iterate through all child declarations
    for (const auto* D : NS->decls()) {
        // Dispatch each child to appropriate handler
        // The dispatcher will route to the correct handler based on type
        bool handled = disp.dispatch(cppASTContext, cASTContext, D);

        if (!handled) {
            // Log warning for unhandled declarations (not fatal in Phase 1)
            llvm::outs() << "[NamespaceHandler] Warning: Unhandled child declaration in namespace\n";
        }
    }
}

} // namespace cpptoc
