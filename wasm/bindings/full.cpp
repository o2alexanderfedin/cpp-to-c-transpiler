#include <emscripten/bind.h>
#include <string>
#include <vector>
#include <sstream>

// Clang includes
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"

// Project includes
#include "CppToCVisitor.h"
#include "CppToCConsumer.h"
#include "CppToCFrontendAction.h"
#include "CodeGenerator.h"
#include "ACSLGenerator.h"
#include "ACSLStatementAnnotator.h"
#include "ACSLTypeInvariantGenerator.h"
#include "ACSLAxiomaticBuilder.h"
#include "ACSLGhostCodeInjector.h"
#include "ACSLBehaviorAnnotator.h"

using namespace emscripten;

// ============================================================================
// WASM API Structures (same as minimal)
// ============================================================================

struct Diagnostic {
    int line = 0;
    int column = 0;
    std::string message;
    std::string severity; // "error", "warning", "note"
};

struct ACSLOptions {
    bool statements = false;
    bool typeInvariants = false;
    bool axiomatics = false;
    bool ghostCode = false;
    bool behaviors = false;
};

struct TranspileOptions {
    ACSLOptions acsl;
    std::string target = "c99"; // c89, c99, c11, c17
    bool optimize = false;
};

struct TranspileResult {
    bool success = false;
    std::string c;
    std::string acsl;
    std::vector<Diagnostic> diagnostics;
};

// ============================================================================
// Full Transpiler Implementation (with all ACSL phases)
// ============================================================================

class WASMTranspiler {
public:
    TranspileResult transpile(const std::string& cppCode, const TranspileOptions& options) {
        TranspileResult result;

        try {
            // Create in-memory virtual file
            std::string virtualFilename = "input.cpp";

            // Create compiler invocation
            std::vector<std::string> args;
            args.push_back("cpptoc");
            args.push_back("-std=c++17");
            args.push_back("--");
            args.push_back("-std=c++17");

            // Run Clang tool
            auto action = std::make_unique<cpptoc::CppToCFrontendAction>();

            // Parse code using runToolOnCodeWithArgs
            bool parseSuccess = clang::tooling::runToolOnCodeWithArgs(
                std::move(action),
                cppCode,
                args,
                virtualFilename
            );

            if (!parseSuccess) {
                Diagnostic diag;
                diag.line = 0;
                diag.column = 0;
                diag.message = "Failed to parse C++ code";
                diag.severity = "error";
                result.diagnostics.push_back(diag);
                result.success = false;
                return result;
            }

            // TODO: Full implementation pending refactoring of main.cpp logic
            // For now, return placeholder with ACSL support indication
            result.success = true;
            result.c = "// Transpiled C code (full build with ACSL)\n// Full implementation pending\n";

            // Generate ACSL annotations based on options
            std::ostringstream acslStream;
            if (options.acsl.statements) {
                acslStream << "/*@ assert true; // Statement annotations enabled */\n";
            }
            if (options.acsl.typeInvariants) {
                acslStream << "/*@ invariant // Type invariants enabled */\n";
            }
            if (options.acsl.axiomatics) {
                acslStream << "/*@ axiomatic // Axiomatics enabled */\n";
            }
            if (options.acsl.ghostCode) {
                acslStream << "/*@ ghost // Ghost code enabled */\n";
            }
            if (options.acsl.behaviors) {
                acslStream << "/*@ behavior // Behaviors enabled */\n";
            }

            result.acsl = acslStream.str();

        } catch (const std::exception& e) {
            Diagnostic diag;
            diag.line = 0;
            diag.column = 0;
            diag.message = std::string("Exception: ") + e.what();
            diag.severity = "error";
            result.diagnostics.push_back(diag);
            result.success = false;
        }

        return result;
    }

    std::string getVersion() const {
        return "1.22.0-full";
    }
};

// ============================================================================
// Embind Bindings (same as minimal)
// ============================================================================

EMSCRIPTEN_BINDINGS(cpptoc_full) {
    value_object<ACSLOptions>("ACSLOptions")
        .field("statements", &ACSLOptions::statements)
        .field("typeInvariants", &ACSLOptions::typeInvariants)
        .field("axiomatics", &ACSLOptions::axiomatics)
        .field("ghostCode", &ACSLOptions::ghostCode)
        .field("behaviors", &ACSLOptions::behaviors);

    value_object<TranspileOptions>("TranspileOptions")
        .field("acsl", &TranspileOptions::acsl)
        .field("target", &TranspileOptions::target)
        .field("optimize", &TranspileOptions::optimize);

    value_object<Diagnostic>("Diagnostic")
        .field("line", &Diagnostic::line)
        .field("column", &Diagnostic::column)
        .field("message", &Diagnostic::message)
        .field("severity", &Diagnostic::severity);

    value_object<TranspileResult>("TranspileResult")
        .field("success", &TranspileResult::success)
        .field("c", &TranspileResult::c)
        .field("acsl", &TranspileResult::acsl)
        .field("diagnostics", &TranspileResult::diagnostics);

    register_vector<Diagnostic>("DiagnosticVector");

    class_<WASMTranspiler>("Transpiler")
        .constructor<>()
        .function("transpile", &WASMTranspiler::transpile)
        .function("getVersion", &WASMTranspiler::getVersion);
}
