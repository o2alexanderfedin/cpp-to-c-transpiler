// TranspilerAPI: Core library implementation for C++ to C transpilation
// Extracts the transpiler logic from main.cpp into a reusable library API

#include "TranspilerAPI.h"
#include "ACSLGenerator.h"
#include "CNodeBuilder.h"
#include "CppToCVisitor.h"
#include "CodeGenerator.h"
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

public:
    TranspilerConsumer(clang::ASTContext &Context,
                      llvm::raw_string_ostream &CStream,
                      llvm::raw_string_ostream &HStream)
        : Context(Context), CStream(CStream), HStream(HStream) {}

    void HandleTranslationUnit(clang::ASTContext &Context) override {
        // Create CNodeBuilder for C AST construction
        clang::CNodeBuilder Builder(Context);

        // Create and run visitor to traverse AST
        CppToCVisitor Visitor(Context, Builder);
        auto *TU = Context.getTranslationUnitDecl();
        Visitor.TraverseDecl(TU);

        // Process template instantiations (Phase 11)
        Visitor.processTemplateInstantiations(TU);

        // Generate C code output using CodeGenerator
        // For now, output to C stream (we'll separate .h/.c in future iterations)
        CodeGenerator CGen(CStream, Context);
        CGen.printTranslationUnit(TU);

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
            CI.getASTContext(), CStream, HStream);
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

        // Run the transpiler using Clang's tooling API
        // This parses the C++ code, builds AST, and runs our visitor
        bool success = clang::tooling::runToolOnCodeWithArgs(
            factory.create(),
            cppSource,
            args,
            filename
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
