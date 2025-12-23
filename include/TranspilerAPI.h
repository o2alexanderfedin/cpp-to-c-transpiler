#pragma once

// TranspilerAPI: Core library interface for C++ to C transpilation
// Designed to be called from both CLI and WASM contexts
//
// SOLID Principles:
// - Single Responsibility: Provides clean API for transpilation
// - Open/Closed: Options struct is open for extension
// - Dependency Inversion: Depends on abstractions (options, results)
//
// This API extracts the core transpiler logic from main.cpp into a reusable library
// that can be called from both CLI (main.cpp) and WASM (bindings/full.cpp).

#include <string>
#include <vector>

namespace cpptoc {

/// @brief Configuration options for transpilation
///
/// This struct consolidates all transpiler options that were previously
/// exposed as CLI flags in main.cpp. It allows the same transpiler logic
/// to be called from different contexts (CLI, WASM, library).
struct TranspileOptions {
    /// @brief ACSL (ANSI/ISO C Specification Language) annotation options
    struct ACSLConfig {
        bool statements = false;         ///< Generate statement-level ACSL annotations
        bool typeInvariants = false;     ///< Generate type invariant annotations
        bool axiomatics = false;         ///< Generate axiomatic definitions
        bool ghostCode = false;          ///< Generate ghost code for verification
        bool behaviors = false;          ///< Generate behavior specifications
        bool memoryPredicates = false;   ///< Generate memory predicates (allocable, freeable, etc.)
    } acsl;

    /// @brief ACSL coverage level
    enum class ACSLLevelEnum {
        Basic,  ///< Function contracts only (requires, ensures, assigns)
        Full    ///< Function contracts + loop invariants + class invariants
    };
    ACSLLevelEnum acslLevel = ACSLLevelEnum::Basic;

    /// @brief ACSL output mode
    enum class ACSLOutputModeEnum {
        Inline,    ///< Annotations inline in generated C code
        Separate   ///< Annotations in separate .acsl files
    };
    ACSLOutputModeEnum acslOutputMode = ACSLOutputModeEnum::Inline;

    /// @brief Target C standard
    std::string target = "c99";        ///< Target C standard (c89, c99, c11, c17)

    /// @brief C++ standard version
    int cppStandard = 17;              ///< C++ standard (11, 14, 17, 20, 23)

    /// @brief Enable optimization
    bool optimize = false;             ///< Enable optimization passes

    /// @brief Template monomorphization options (Phase 11)
    bool monomorphizeTemplates = true;           ///< Enable template monomorphization
    unsigned int templateInstantiationLimit = 1000; ///< Maximum template instantiations

    /// @brief Exception handling options (Phase 12)
    bool enableExceptions = true;      ///< Enable exception handling translation
    std::string exceptionModel = "sjlj"; ///< Exception model (sjlj, tables)

    /// @brief RTTI options (Phase 13)
    bool enableRTTI = true;            ///< Enable RTTI translation (typeid, dynamic_cast)

    /// @brief Output format options
    bool usePragmaOnce = false;        ///< Use #pragma once instead of include guards

    /// @brief Dependency visualization options
    bool generateDependencyGraph = false; ///< Generate dependency graph in DOT format

    /// @brief Virtual files for in-memory compilation
    /// @details Each pair represents (file_path, file_content).
    ///          Used to provide header files without filesystem access.
    ///          Example: {"/usr/include/stdio.h", "... header content ..."}
    /// @note Paths should be absolute and match -I include directories
    std::vector<std::pair<std::string, std::string>> virtualFiles;
};

/// @brief Diagnostic message from transpilation
///
/// Captures errors, warnings, and notes generated during transpilation.
/// Maps to Clang's diagnostic system output.
struct Diagnostic {
    int line = 0;                      ///< Source line number (0 if not applicable)
    int column = 0;                    ///< Source column number (0 if not applicable)
    std::string message;               ///< Diagnostic message text
    std::string severity;              ///< Severity level: "error", "warning", "note"
};

/// @brief Result of transpilation operation
///
/// Contains all generated code and diagnostics from the transpilation process.
/// Designed to work in both CLI (writes to files) and WASM (returns strings).
struct TranspileResult {
    bool success = false;              ///< True if transpilation succeeded
    std::string c;                     ///< Generated C implementation code (.c file)
    std::string h;                     ///< Generated C header code (.h file)
    std::string acsl;                  ///< ACSL annotations (if separate mode enabled)
    std::string dependencyGraph;       ///< DOT dependency graph (if requested)
    std::vector<Diagnostic> diagnostics; ///< All diagnostic messages
};

/// @brief Main transpiler function
///
/// Transpiles C++ source code to C using the configured options.
/// This function replaces the main.cpp logic and can be called from any context.
///
/// Implementation strategy:
/// - Uses Clang's runToolOnCodeWithArgs() for in-memory compilation
/// - Captures output using llvm::raw_string_ostream instead of stdout
/// - Collects diagnostics in vector
/// - Returns TranspileResult with generated code
///
/// @param cppSource C++ source code to transpile
/// @param filename Source filename (for error messages and #line directives)
/// @param options Transpilation configuration options
/// @return TranspileResult containing generated code and diagnostics
///
/// Example usage:
/// @code
///   cpptoc::TranspileOptions opts;
///   opts.acsl.statements = true;
///   opts.cppStandard = 17;
///   auto result = cpptoc::transpile("int main() { return 0; }", "test.cpp", opts);
///   if (result.success) {
///     std::cout << result.c << std::endl;
///   }
/// @endcode
TranspileResult transpile(
    const std::string& cppSource,
    const std::string& filename = "input.cpp",
    const TranspileOptions& options = TranspileOptions()
);

} // namespace cpptoc
