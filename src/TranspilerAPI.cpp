// TranspilerAPI: Core library implementation for C++ to C transpilation
// Extracts the transpiler logic from main.cpp into a reusable library API

#include "TranspilerAPI.h"
#include "ACSLGenerator.h"
#include "CNodeBuilder.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "dispatch/TranslationUnitHandler.h"
#include "dispatch/NamespaceHandler.h"
#include "dispatch/RecordHandler.h"
#include "dispatch/FunctionHandler.h"
#include "dispatch/InstanceMethodHandler.h"
#include "dispatch/StaticMethodHandler.h"
#include "dispatch/VirtualMethodHandler.h"
// TODO: ConstructorHandler needs to be updated to dispatcher pattern
// #include "dispatch/ConstructorHandler.h"
#include "dispatch/TypeHandler.h"
#include "dispatch/ParameterHandler.h"
#include "dispatch/CompoundStmtHandler.h"
#include "dispatch/ReturnStmtHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/MemberExprHandler.h"
#include "dispatch/ArraySubscriptExprHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/UnaryOperatorHandler.h"
#include "dispatch/BinaryOperatorHandler.h"
#include "dispatch/ParenExprHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/CXXOperatorCallExprHandler.h"
#include "dispatch/CXXTypeidExprHandler.h"
#include "dispatch/CXXDynamicCastExprHandler.h"
#include "dispatch/CommaOperatorHandler.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "CodeGenerator.h"
#include "HeaderSeparator.h"
#include "IncludeGuardGenerator.h"
#include "TargetContext.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>
#include <memory>

namespace cpptoc {

// Global state for options (needed by visitor and other components)
// The visitor and annotators use extern functions to access options,
// so we need to provide implementations that read from this global state.
static const TranspileOptions* g_currentOptions = nullptr;

// Accessor functions (replace main.cpp global functions)
// These are called by CppToCVisitor and other components to get configuration.
// They are declared extern in CppToCVisitor.cpp (lines 13-21).

/// @brief Check if any ACSL option is enabled
bool shouldGenerateACSL() {
    if (!g_currentOptions) return false;

    const auto& acsl = g_currentOptions->acsl;
    return acsl.statements || acsl.typeInvariants || acsl.axiomatics ||
           acsl.ghostCode || acsl.behaviors || acsl.memoryPredicates;
}

/// @brief Get ACSL coverage level from options
ACSLLevel getACSLLevel() {
    if (!g_currentOptions) return ACSLLevel::Basic;

    return (g_currentOptions->acslLevel == TranspileOptions::ACSLLevelEnum::Full)
        ? ACSLLevel::Full
        : ACSLLevel::Basic;
}

/// @brief Get ACSL output mode from options
ACSLOutputMode getACSLOutputMode() {
    if (!g_currentOptions) return ACSLOutputMode::Inline;

    return (g_currentOptions->acslOutputMode == TranspileOptions::ACSLOutputModeEnum::Separate)
        ? ACSLOutputMode::Separate
        : ACSLOutputMode::Inline;
}

/// @brief Check if memory predicates should be generated (Phase 6)
bool shouldGenerateMemoryPredicates() {
    if (!g_currentOptions) return false;
    return g_currentOptions->acsl.memoryPredicates;
}

/// @brief Check if templates should be monomorphized (Phase 11)
bool shouldMonomorphizeTemplates() {
    if (!g_currentOptions) return true; // Default: enabled
    return g_currentOptions->monomorphizeTemplates;
}

/// @brief Get template instantiation limit (Phase 11)
unsigned int getTemplateInstantiationLimit() {
    if (!g_currentOptions) return 1000; // Default limit
    return g_currentOptions->templateInstantiationLimit;
}

/// @brief Check if exception handling should be enabled (Phase 12)
bool shouldEnableExceptions() {
    if (!g_currentOptions) return true; // Default: enabled
    return g_currentOptions->enableExceptions;
}

/// @brief Get exception handling model (Phase 12)
std::string getExceptionModel() {
    if (!g_currentOptions) return "sjlj"; // Default: SJLJ model
    return g_currentOptions->exceptionModel;
}

/// @brief Check if RTTI should be enabled (Phase 13)
bool shouldEnableRTTI() {
    if (!g_currentOptions) return true; // Default: enabled
    return g_currentOptions->enableRTTI;
}

/// @brief Check if #pragma once should be used
bool shouldUsePragmaOnce() {
    if (!g_currentOptions) return false; // Default: use include guards
    return g_currentOptions->usePragmaOnce;
}

// Custom ASTConsumer that captures output to string streams
class TranspilerConsumer : public clang::ASTConsumer {
    clang::ASTContext &Context;
    llvm::raw_string_ostream &CStream;
    llvm::raw_string_ostream &HStream;
    std::string Filename;

public:
    TranspilerConsumer(clang::ASTContext &Context,
                      llvm::raw_string_ostream &CStream,
                      llvm::raw_string_ostream &HStream,
                      const std::string &Filename)
        : Context(Context), CStream(CStream), HStream(HStream), Filename(Filename) {}

    void HandleTranslationUnit(clang::ASTContext &Context) override {
        // Setup target context for C AST
        TargetContext& targetCtx = TargetContext::getInstance();
        clang::ASTContext& cCtx = targetCtx.getContext();

        // Create mapping utilities
        cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance(".", ".");
        cpptoc::DeclLocationMapper locMapper(mapper);

        // Get singleton mapper instances (shared across all source files)
        cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
        cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
        cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
        cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

        // Create dispatcher with all mappers
        CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

        // Register all handlers in dependency order
        // Base handlers first (these are used by others)
        cpptoc::TypeHandler::registerWith(dispatcher);
        cpptoc::ParameterHandler::registerWith(dispatcher);

        // Expression handlers
        cpptoc::LiteralHandler::registerWith(dispatcher);
        cpptoc::DeclRefExprHandler::registerWith(dispatcher);
        cpptoc::MemberExprHandler::registerWith(dispatcher);
        cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);
        cpptoc::ParenExprHandler::registerWith(dispatcher);
        cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
        cpptoc::UnaryOperatorHandler::registerWith(dispatcher);
        cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
        cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);
        cpptoc::CXXTypeidExprHandler::registerWith(dispatcher);
        cpptoc::CXXDynamicCastExprHandler::registerWith(dispatcher);
        cpptoc::CommaOperatorHandler::registerWith(dispatcher);

        // Statement handlers
        cpptoc::CompoundStmtHandler::registerWith(dispatcher);
        cpptoc::ReturnStmtHandler::registerWith(dispatcher);

        // Declaration handlers
        cpptoc::RecordHandler::registerWith(dispatcher);
        cpptoc::FunctionHandler::registerWith(dispatcher);
        // TODO: Re-enable when ConstructorHandler is updated to dispatcher pattern
        // cpptoc::ConstructorHandler::registerWith(dispatcher);
        cpptoc::InstanceMethodHandler::registerWith(dispatcher);
        cpptoc::StaticMethodHandler::registerWith(dispatcher);
        cpptoc::VirtualMethodHandler::registerWith(dispatcher);
        cpptoc::NamespaceHandler::registerWith(dispatcher);
        cpptoc::TranslationUnitHandler::registerWith(dispatcher);

        // Traverse and dispatch AST nodes
        auto *TU = Context.getTranslationUnitDecl();
        dispatcher.dispatch(Context, cCtx, TU);

        // Separate declarations into header and implementation (Phase 28)
        HeaderSeparator separator;
        separator.analyzeTranslationUnit(TU);

        // Generate include guards for header
        IncludeGuardGenerator guardGen(g_currentOptions ? g_currentOptions->usePragmaOnce : false);
        std::string guardName = guardGen.generateGuardName(Filename + ".h");

        // Write header file (.h)
        HStream << guardGen.emitGuardBegin(guardName);
        HStream << "\n";

        // Forward declarations
        const auto& forwardDecls = separator.getForwardDecls();
        if (!forwardDecls.empty()) {
            HStream << "// Forward declarations\n";
            for (const auto& fwd : forwardDecls) {
                HStream << "struct " << fwd << ";\n";
            }
            HStream << "\n";
        }

        // Header declarations (structs, function prototypes)
        CodeGenerator HGen(HStream, Context);
        for (clang::Decl* decl : separator.getHeaderDecls()) {
            HGen.printDecl(decl, /*declarationOnly=*/true);
        }

        HStream << guardGen.emitGuardEnd(guardName);

        // Write implementation file (.c)
        CStream << "#include \"" << Filename << ".h\"\n\n";

        // Implementation (function bodies)
        CodeGenerator CGen(CStream, Context);
        for (clang::Decl* decl : separator.getImplDecls()) {
            CGen.printDecl(decl, /*declarationOnly=*/false);
        }

        // Flush streams to ensure all output is captured
        CStream.flush();
        HStream.flush();
    }
};

// Custom FrontendAction that uses our TranspilerConsumer
class TranspilerAction : public clang::ASTFrontendAction {
    llvm::raw_string_ostream &CStream;
    llvm::raw_string_ostream &HStream;

public:
    TranspilerAction(llvm::raw_string_ostream &CStream,
                    llvm::raw_string_ostream &HStream)
        : CStream(CStream), HStream(HStream) {}

    std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
        clang::CompilerInstance &CI,
        llvm::StringRef file) override {
        return std::make_unique<TranspilerConsumer>(
            CI.getASTContext(), CStream, HStream, file.str());
    }
};

// Custom FrontendActionFactory that creates TranspilerAction instances
class TranspilerActionFactory : public clang::tooling::FrontendActionFactory {
    llvm::raw_string_ostream &CStream;
    llvm::raw_string_ostream &HStream;

public:
    TranspilerActionFactory(llvm::raw_string_ostream &CStream,
                           llvm::raw_string_ostream &HStream)
        : CStream(CStream), HStream(HStream) {}

    std::unique_ptr<clang::FrontendAction> create() override {
        return std::make_unique<TranspilerAction>(CStream, HStream);
    }
};

/// @brief Main transpiler function
///
/// This function implements the core transpilation logic using Clang's
/// tooling API to run the transpiler in-memory without requiring file I/O.
///
/// Implementation approach:
/// 1. Set global options for visitor access
/// 2. Create Clang compiler arguments based on options
/// 3. Create custom FrontendAction that captures output to string streams
/// 4. Use runToolOnCodeWithArgs() to run transpiler in-memory
/// 5. Collect generated C code from string streams
/// 6. Collect diagnostics (future enhancement)
/// 7. Clear global options
///
/// The function follows the same flow as main.cpp (lines 183-244) but
/// adapted for library usage without file I/O.
TranspileResult transpile(
    const std::string& cppSource,
    const std::string& filename,
    const TranspileOptions& options
) {
    TranspileResult result;

    // Set global options for visitor and annotator access
    // This is required because CppToCVisitor uses extern accessor functions
    g_currentOptions = &options;

    try {
        // Build compiler arguments based on options
        std::vector<std::string> args;

        // Set C++ standard
        args.push_back("-std=c++" + std::to_string(options.cppStandard));

        // Add common flags needed for transpilation
        args.push_back("-fsyntax-only");  // Don't generate code, just parse
        args.push_back("-fno-color-diagnostics"); // Plain text diagnostics

        // Disable some C++ features that complicate transpilation
        if (!options.enableExceptions) {
            args.push_back("-fno-exceptions");
        }
        if (!options.enableRTTI) {
            args.push_back("-fno-rtti");
        }

        // Create string buffers and streams for output capture
        std::string cCodeBuffer;
        std::string hCodeBuffer;
        llvm::raw_string_ostream cStream(cCodeBuffer);
        llvm::raw_string_ostream hStream(hCodeBuffer);

        // Create custom action factory that captures output
        TranspilerActionFactory factory(cStream, hStream);

        // Build FileContentMappings from virtual files
        clang::tooling::FileContentMappings virtualMappedFiles;
        for (const auto& [path, content] : options.virtualFiles) {
            virtualMappedFiles.push_back({path, content});
        }

        // Run the transpiler using Clang's tooling API with virtual files support
        // This parses the C++ code, builds AST, and runs our visitor
        bool success = clang::tooling::runToolOnCodeWithArgs(
            factory.create(),
            cppSource,
            args,
            filename,
            "cpptoc-transpiler",  // tool name
            std::make_shared<clang::PCHContainerOperations>(),
            virtualMappedFiles  // virtual files
        );

        // Flush streams to ensure all output is captured
        cStream.flush();
        hStream.flush();

        // Store results
        result.success = success;
        result.c = cCodeBuffer;
        result.h = hCodeBuffer;

        // If transpilation failed but we don't have diagnostics, add a generic error
        if (!success && result.diagnostics.empty()) {
            Diagnostic error;
            error.severity = "error";
            error.message = "Transpilation failed - see compiler diagnostics";
            result.diagnostics.push_back(error);
        }

    } catch (const std::exception& e) {
        // Catch any errors and return them as diagnostics
        Diagnostic error;
        error.severity = "error";
        error.message = std::string("Transpilation failed: ") + e.what();
        result.diagnostics.push_back(error);
        result.success = false;
    }

    // Clear global options to prevent stale state
    g_currentOptions = nullptr;

    return result;
}

} // namespace cpptoc

// Export accessor functions in global namespace for compatibility
// These are declared as extern in CppToCVisitor.cpp and other files
// We implement them as wrappers that call the cpptoc:: versions

bool shouldGenerateACSL() {
    return cpptoc::shouldGenerateACSL();
}

ACSLLevel getACSLLevel() {
    return cpptoc::getACSLLevel();
}

ACSLOutputMode getACSLOutputMode() {
    return cpptoc::getACSLOutputMode();
}

bool shouldGenerateMemoryPredicates() {
    return cpptoc::shouldGenerateMemoryPredicates();
}

bool shouldMonomorphizeTemplates() {
    return cpptoc::shouldMonomorphizeTemplates();
}

unsigned int getTemplateInstantiationLimit() {
    return cpptoc::getTemplateInstantiationLimit();
}

bool shouldEnableExceptions() {
    return cpptoc::shouldEnableExceptions();
}

std::string getExceptionModel() {
    return cpptoc::getExceptionModel();
}

bool shouldEnableRTTI() {
    return cpptoc::shouldEnableRTTI();
}

bool shouldUsePragmaOnce() {
    return cpptoc::shouldUsePragmaOnce();
}
