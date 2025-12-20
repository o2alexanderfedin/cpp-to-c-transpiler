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

using namespace emscripten;

// ============================================================================
// WASM API Structures
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
// Transpiler Implementation
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

            // For minimal build, just return a placeholder
            // Full transpiler integration requires refactoring main.cpp logic
            result.success = true;
            result.c = "// Transpiled C code (minimal build)\n// Full implementation pending\n";
            result.acsl = "";

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
        return "1.22.0-minimal";
    }
};

// ============================================================================
// Embind Bindings
// ============================================================================

EMSCRIPTEN_BINDINGS(cpptoc_minimal) {
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
