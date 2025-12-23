#include <emscripten/bind.h>
#include <string>
#include <vector>
#include <sstream>
#include "TranspilerAPI.h"

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
    bool memoryPredicates = false;
};

struct TranspileOptions {
    ACSLOptions acsl;
    std::string target = "c99"; // c89, c99, c11, c17
    bool optimize = false;
    bool monomorphizeTemplates = true;
    bool enableExceptions = true;
    std::string exceptionModel = "sjlj";
    bool enableRTTI = true;
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
            // Map WASM options to library options
            cpptoc::TranspileOptions libOpts;

            // ACSL configuration
            libOpts.acsl.statements = options.acsl.statements;
            libOpts.acsl.typeInvariants = options.acsl.typeInvariants;
            libOpts.acsl.axiomatics = options.acsl.axiomatics;
            libOpts.acsl.ghostCode = options.acsl.ghostCode;
            libOpts.acsl.behaviors = options.acsl.behaviors;
            libOpts.acsl.memoryPredicates = options.acsl.memoryPredicates;

            // Other options
            libOpts.target = options.target;
            libOpts.optimize = options.optimize;
            libOpts.monomorphizeTemplates = options.monomorphizeTemplates;
            libOpts.enableExceptions = options.enableExceptions;
            libOpts.exceptionModel = options.exceptionModel;
            libOpts.enableRTTI = options.enableRTTI;

            // Call the real transpiler API
            cpptoc::TranspileResult libResult = cpptoc::transpile(cppCode, "input.cpp", libOpts);

            // Map library result to WASM result
            result.success = libResult.success;
            result.c = libResult.c;
            result.acsl = libResult.acsl;

            // Map diagnostics
            for (const auto& libDiag : libResult.diagnostics) {
                Diagnostic wasmDiag;
                wasmDiag.line = libDiag.line;
                wasmDiag.column = libDiag.column;
                wasmDiag.message = libDiag.message;
                wasmDiag.severity = libDiag.severity;
                result.diagnostics.push_back(wasmDiag);
            }

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
        .field("behaviors", &ACSLOptions::behaviors)
        .field("memoryPredicates", &ACSLOptions::memoryPredicates);

    value_object<TranspileOptions>("TranspileOptions")
        .field("acsl", &TranspileOptions::acsl)
        .field("target", &TranspileOptions::target)
        .field("optimize", &TranspileOptions::optimize)
        .field("monomorphizeTemplates", &TranspileOptions::monomorphizeTemplates)
        .field("enableExceptions", &TranspileOptions::enableExceptions)
        .field("exceptionModel", &TranspileOptions::exceptionModel)
        .field("enableRTTI", &TranspileOptions::enableRTTI);

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
