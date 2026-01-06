<?xml version="1.0" encoding="UTF-8"?>
<pipeline_research>
  <current_architecture>
    <entry_points>
      <file path="src/main.cpp">
        <responsibilities>
          - Main CLI entry point for cpptoc transpiler
          - Command line argument parsing (llvm::cl options)
          - Source file discovery (recursive .cpp/.cxx/.cc search)
          - Clang tooling invocation (ClangTool with FrontendActionFactory)
          - Dependency visualization (optional)
          - Global configuration accessors (extern functions)
        </responsibilities>
        <cli_parsing>
          Uses llvm::cl::OptionCategory with options:
          - --source-dir (REQUIRED): Project root for auto-discovery
          - --output-dir: Output directory for generated files
          - --use-pragma-once: Include guard style
          - --generate-acsl: ACSL annotation generation
          - --acsl-level: Basic or Full coverage
          - --acsl-output: Inline or Separate files
          - --template-monomorphization: Enable/disable (default on)
          - --enable-exceptions: Exception handling translation (default on)
          - --enable-rtti: RTTI translation (default on)

          Parsed via CommonOptionsParser::create() at line 359
          Global accessor functions (lines 190-247) provide config to other components
        </cli_parsing>
        <file_discovery>
          Auto-discovery mode (lines 282-329):
          - Recursively scans --source-dir for .cpp/.cxx/.cc files
          - Excludes: .git, .svn, build*, cmake-build-*, node_modules, vendor, hidden dirs
          - Returns vector of absolute paths
          - Sorts files to process main.cpp LAST (bug fix for constructor/method map)

          Discovery happens BEFORE Clang tooling invocation
          Individual file arguments are IGNORED (project-based transpilation only)
        </file_discovery>
        <clang_tooling_invocation>
          Creates ClangTool (line 427):
          ClangTool Tool(OptionsParser.getCompilations(), sourceFiles);

          Adds argument adjusters:
          - Strip output adjuster
          - Suppress all warnings (-Wno-everything)

          Runs tool (line 443):
          Tool.run(newFrontendActionFactory&lt;CppToCFrontendAction&gt;().get())

          One FrontendAction instance per source file (Clang behavior)
        </clang_tooling_invocation>
      </file>

      <file path="src/TranspilerAPI.cpp">
        <responsibilities>
          - Library API for in-memory transpilation (no file I/O)
          - Provides transpile() function for programmatic usage
          - Custom FrontendAction/ASTConsumer for string stream output
          - Global configuration management (g_currentOptions pointer)
          - Accessor function implementations (bridge to main.cpp extern functions)
        </responsibilities>
        <api_design>
          Function signature (lines 292-296):
          TranspileResult transpile(
            const std::string&amp; cppSource,
            const std::string&amp; filename,
            const TranspileOptions&amp; options
          )

          Returns: struct with success flag, generated C code (.c/.h), diagnostics

          Uses custom TranspilerConsumer (lines 131-241) that:
          - Creates CppToCVisitorDispatcher inline
          - Registers all handlers
          - Dispatches on TranslationUnitDecl
          - Uses HeaderSeparator for .h/.c split
          - Captures output to string streams (not files)
        </api_design>
        <virtual_files_support>
          Supports virtual file mappings (line 333):
          FileContentMappings virtualMappedFiles from options.virtualFiles

          Enables in-memory transpilation with:
          runToolOnCodeWithArgs(..., virtualMappedFiles)

          Useful for testing and web-based transpiler
        </virtual_files_support>
      </file>

      <file path="src/CppToCFrontendAction.cpp">
        <responsibilities>
          - Implements CppToCFrontendAction (Clang FrontendAction)
          - Creates DispatcherConsumer (custom ASTConsumer) inline
          - Entry point for per-file C++ AST processing
          - Bridge between Clang tooling and dispatcher architecture
        </responsibilities>
        <consumer_creation>
          CreateASTConsumer() (lines 173-178):
          - Gets source directory from extern getSourceDir()
          - Creates DispatcherConsumer with filename and sourceDir
          - Called once per source file by Clang
        </consumer_creation>
        <dispatcher_consumer>
          DispatcherConsumer (lines 47-169):
          - Holds InputFilename and SourceDir
          - HandleTranslationUnit() is main entry point (line 55)

          Workflow:
          1. Get TargetContext singleton (shared C ASTContext)
          2. Get PathMapper singleton with sourceDir/outputDir
          3. Map source file to target path
          4. Get/create C_TranslationUnit for target path
          5. Create all mappers (DeclLocationMapper, DeclMapper, TypeMapper, ExprMapper, StmtMapper)
          6. Create CppToCVisitorDispatcher with all mappers
          7. Register ALL handlers in dependency order (lines 84-107)
          8. Dispatch on C++ TranslationUnitDecl (line 111)
          9. Generate C code using CodeGenerator (lines 113-147)
          10. Write files using FileOutputManager (lines 149-167)

          PROBLEM: Mixing concerns - combines dispatcher setup, code generation, AND file I/O
        </dispatcher_consumer>
      </file>
    </entry_points>

    <cpp_ast_parsing>
      <clang_tooling_usage>
        Two paths for Clang invocation:

        1. CLI path (main.cpp):
           - ClangTool with FrontendActionFactory
           - Tool.run(newFrontendActionFactory&lt;CppToCFrontendAction&gt;())
           - Processes multiple files via ClangTool's internal iteration
           - Each file gets own CompilerInstance and ASTContext

        2. Library path (TranspilerAPI.cpp):
           - runToolOnCodeWithArgs() for single-file in-memory
           - Custom TranspilerActionFactory
           - Virtual file mappings support
           - Single ASTContext per call

        Both paths create separate C++ ASTContext per source file (Clang requirement)
      </clang_tooling_usage>

      <translation_unit_creation>
        C++ Translation Units:
        - One C++ TU per source file (created by Clang frontend)
        - Each has own ASTContext (immutable, source)
        - CompilerInstance creates and owns C++ ASTContext
        - TU root: clang::TranslationUnitDecl from Context.getTranslationUnitDecl()

        C Translation Units:
        - ONE shared C ASTContext (TargetContext singleton)
        - One C TU per OUTPUT file (PathMapper.getOrCreateTU())
        - Multiple source files can map to same C TU (header + impl)
        - C TU root: clang::TranslationUnitDecl::Create(cCtx)
        - Managed by PathMapper: fileToTU_ map (target path → C_TU)
      </translation_unit_creation>

      <ast_consumer_pattern>
        Clang ASTConsumer interface:
        - HandleTranslationUnit(ASTContext&amp;) is main entry point
        - Called AFTER Clang finishes parsing entire file
        - Receives fully-built C++ AST

        Two consumer implementations:

        1. DispatcherConsumer (CppToCFrontendAction.cpp, lines 47-169):
           - File-based output (writes .h/.c files)
           - Inline creation of dispatcher + mappers + handlers
           - Inline code generation and file writing
           - Used by main.cpp CLI tool

        2. TranspilerConsumer (TranspilerAPI.cpp, lines 131-241):
           - String-based output (returns strings)
           - Inline creation of dispatcher + mappers + handlers
           - Uses HeaderSeparator for .h/.c split
           - Used by library API

        BOTH consumers have same structure:
        1. Setup TargetContext and PathMapper
        2. Create all mappers
        3. Create dispatcher
        4. Register all handlers (DUPLICATE CODE - 24 handlers each)
        5. Dispatch on TU
        6. Generate code
        7. Output (files vs strings)

        PROBLEM: Handler registration duplicated in 2 places
        PROBLEM: Consumer mixes dispatcher setup + code generation + output
      </ast_consumer_pattern>
    </cpp_ast_parsing>

    <dispatcher_transformation>
      <handler_registration>
        Registration happens in TWO places (duplicate code):

        1. DispatcherConsumer::HandleTranslationUnit() (CppToCFrontendAction.cpp, lines 84-107)
        2. TranspilerConsumer::HandleTranslationUnit() (TranspilerAPI.cpp, lines 162-192)

        Handlers registered in DEPENDENCY ORDER:
        - TypeHandler, ParameterHandler (base handlers, used by others)
        - Expression handlers (12 handlers: literals, refs, operators, casts, etc.)
        - Statement handlers (2 handlers: compound, return)
        - Declaration handlers (8 handlers: record, function, methods, namespace, TU)

        Total: 24 handlers

        Pattern for each handler:
        HandlerClass::registerWith(dispatcher);

        Handler implementation (RecordHandler example):
        static void registerWith(CppToCVisitorDispatcher&amp; disp) {
          disp.addHandler(canHandle, handleNode);
        }

        canHandle: Predicate function (checks if node matches)
        handleNode: Visitor function (transforms C++ node → C node)
      </handler_registration>

      <cpp_to_c_transform>
        Dispatcher workflow:
        1. dispatcher.dispatch(cppASTContext, cASTContext, cppNode)
        2. Iterate through registered handlers
        3. Check predicate: if (predicate(cppNode)) ...
        4. Call visitor: handler(dispatcher, cppASTContext, cASTContext, cppNode)
        5. Return true if handled, false otherwise

        Visitor pattern (handler implementation):
        - Receives: dispatcher reference, both ASTContexts, C++ node
        - Extracts info from C++ node (name, type, children, etc.)
        - Translates C++ constructs to C equivalents
        - Uses CNodeBuilder to create C AST nodes
        - Uses mappers to track C++ → C relationships
        - Recursively dispatches child nodes via dispatcher
        - Adds C nodes to appropriate C_TU

        Example: RecordHandler
        - Matches: CXXRecordDecl (C++ class/struct)
        - Translates: class → struct, fields, nested structs
        - Creates: C RecordDecl with FieldDecls
        - Adds to: C_TU for target output file
        - Recursion: Dispatches field types via TypeHandler

        Example: FunctionHandler
        - Matches: FunctionDecl (free functions only, NOT methods)
        - Translates: signature, parameters (references → pointers)
        - Creates: C FunctionDecl with parameter list
        - Body: Currently nullptr (statement translation in progress)
        - Adds to: C_TU for target output file
      </cpp_to_c_transform>

      <shared_c_ast>
        Architecture:
        - ONE TargetContext singleton (entire program lifetime)
        - ONE shared C ASTContext (all files share it)
        - MANY C TranslationUnits (one per output file)

        TargetContext responsibilities:
        - Create and own shared C ASTContext
        - Create C TranslationUnits on demand
        - Global deduplication (findEnum, findStruct, findTypedef)
        - Shared maps (ctorMap, methodMap, dtorMap for multi-file calls)
        - Node location tracking (node → output file path)

        PathMapper responsibilities:
        - Map source paths to target paths
        - Cache C_TU instances (fileToTU_ map)
        - Track declarations to output files (declToTarget_ map)
        - Normalize paths

        Mappers track C++ → C relationships:
        - DeclMapper: C++ Decl → C Decl
        - TypeMapper: C++ Type → C Type
        - ExprMapper: C++ Expr → C Expr
        - StmtMapper: C++ Stmt → C Stmt
        - All use template NodeMapper&lt;K, V&gt; base class

        Cross-file coordination:
        - Handlers use TargetContext.getCtorMap() to find constructors from other files
        - Handlers use TargetContext.findStruct() to avoid duplicate struct definitions
        - PathMapper.getOrCreateTU() ensures one C_TU per output file
        - DeclLocationMapper uses PathMapper to determine output file for each node
      </shared_c_ast>
    </dispatcher_transformation>

    <c_code_generation>
      <code_generator_usage>
        CodeGenerator class (include/CodeGenerator.h):
        - Single Responsibility: Generate C code from C AST
        - Uses Clang's DeclPrinter/StmtPrinter internally (don't reinvent wheel)
        - Configured with C99 PrintingPolicy

        Constructor (line 25):
        CodeGenerator(llvm::raw_ostream&amp; OS, clang::ASTContext&amp; Ctx, const std::string&amp; currentFile)

        Key methods:
        - printDecl(Decl* D, bool declarationOnly) - print one declaration
        - printStmt(Stmt* S, unsigned Indent) - print one statement
        - printTranslationUnit(TranslationUnitDecl* TU) - print all decls

        Special handling:
        - References → pointers conversion (convertToCType)
        - Struct prefix for record types (printCType)
        - Typedef enum generation (printEnumDecl)
        - Function signature vs body (declarationOnly flag)
        - RecoveryExpr detection (containsRecoveryExpr)

        Usage in DispatcherConsumer (lines 113-147):
        1. Create two CodeGenerator instances (header + impl)
        2. Generate header: iterate C_TU decls, printDecl(D, true)
        3. Generate impl: iterate C_TU decls, printDecl(D, false)
        4. Add #pragma once to header
        5. Add #include to impl
      </code_generator_usage>

      <file_emission>
        FileOutputManager class (include/FileOutputManager.h):
        - Single Responsibility: Write generated code to files
        - Determines output filenames from input filename + options
        - Preserves directory structure (sourceDir → outputDir mapping)

        Configuration methods:
        - setInputFilename(filename) - derive default output names
        - setOutputDir(dir) - output directory
        - setSourceDir(root) - source root for structure preservation

        Output methods:
        - writeFiles(headerContent, implContent) - write one file pair
        - writeMultiFileOutput(files) - write multiple file pairs

        Filename calculation:
        - Input: "Point.cpp" → Output: "Point.h" + "Point.c"
        - With sourceDir: "src/Point.cpp" → "output/Point.h" + "output/Point.c"
        - Preserves subdirectories: "src/util/Point.cpp" → "output/util/Point.h"

        Usage in DispatcherConsumer (lines 149-167):
        1. Create FileOutputManager
        2. Set input filename, output dir, source dir
        3. Call writeFiles(headerContent, implContent)
        4. Increment g_filesGeneratedCount on success

        File I/O:
        - Creates directories as needed (mkdir -p behavior)
        - Handles write errors gracefully
        - Returns bool success flag
      </file_emission>

      <header_separation>
        HeaderSeparator (used in TranspilerAPI.cpp, not DispatcherConsumer):
        - Analyzes TranslationUnitDecl to separate declarations
        - Forward declarations (incomplete types)
        - Header declarations (structs, function prototypes)
        - Implementation declarations (function bodies)

        IncludeGuardGenerator:
        - Generates #pragma once or traditional guards
        - Configurable via --use-pragma-once flag

        DispatcherConsumer uses simple approach:
        - Header: all decls with declarationOnly=true
        - Impl: all decls with declarationOnly=false
        - No sophisticated separation logic

        TranspilerConsumer uses HeaderSeparator:
        - More sophisticated .h/.c split
        - Forward declarations
        - Better for library API
      </header_separation>
    </c_code_generation>
  </current_architecture>

  <pipeline_boundaries>
    <stage name="CLI Args Parser">
      <input>
        - Command line arguments (argc, argv)
        - Environment variables (none currently)
      </input>
      <process>
        - Parse options via llvm::cl::CommonOptionsParser
        - Validate option dependencies (e.g., --acsl-level requires --generate-acsl)
        - Store parsed values in global llvm::cl::opt variables
        - Provide accessor functions for other components
      </process>
      <output>
        - Parsed options (source dir, output dir, feature flags)
        - CommonOptionsParser instance (contains CompilationDatabase)
        - Global accessor functions (shouldGenerateACSL(), etc.)
      </output>
      <side_effects>
        - Writes error messages to llvm::errs() on parse failure
        - Exits process (return 1) on invalid options
        - Sets global state via llvm::cl::opt variables
      </side_effects>
      <dependencies>
        - llvm/Support/CommandLine.h
        - clang/Tooling/CommonOptionsParser.h
        - No other cpptoc components
      </dependencies>
    </stage>

    <stage name="Input File Iterator">
      <input>
        - Source directory path (from --source-dir)
        - Exclusion patterns (hardcoded: .git, build*, etc.)
      </input>
      <process>
        - Recursively scan source directory (std::filesystem)
        - Filter by extension (.cpp, .cxx, .cc)
        - Exclude blacklisted directories
        - Sort files (main.cpp last)
        - Return absolute paths
      </process>
      <output>
        - Vector of absolute source file paths
        - Empty vector if no files found
      </output>
      <side_effects>
        - Reads filesystem (directory traversal)
        - Logs discovered file count to llvm::outs()
        - May skip files due to permission errors
      </side_effects>
      <dependencies>
        - std::filesystem
        - No other cpptoc components
      </dependencies>
      <current_location>
        - Implemented in main.cpp (lines 254-329)
        - Functions: isCppSourceFile(), shouldExcludeDirectory(), discoverSourceFiles()
      </current_location>
      <problems>
        - Tightly coupled to main.cpp (not reusable)
        - Hardcoded exclusion patterns (not configurable)
        - No support for explicit file lists (always discovers all files)
      </problems>
    </stage>

    <stage name="C++ AST Parser">
      <input>
        - Vector of source file paths
        - CompilationDatabase (from CommonOptionsParser)
        - Compiler arguments (added via appendArgumentsAdjuster)
      </input>
      <process>
        - Create ClangTool with file list and compilation database
        - Add argument adjusters (-Wno-everything, etc.)
        - For each source file:
          - Create CompilerInstance
          - Parse C++ code via Clang frontend
          - Build C++ AST (one per file)
          - Call FrontendAction::CreateASTConsumer()
          - Call ASTConsumer::HandleTranslationUnit()
        - Collect results (success/failure per file)
      </process>
      <output>
        - Per-file C++ AST (clang::ASTContext, clang::TranslationUnitDecl)
        - Delivered via ASTConsumer::HandleTranslationUnit() callback
        - Return code: 0 if all files succeeded, non-zero on error
      </output>
      <side_effects>
        - Reads source files from disk
        - May read system headers (if available)
        - Writes diagnostics to stderr
        - Increments g_filesGeneratedCount (global state)
      </side_effects>
      <dependencies>
        - clang/Tooling/Tooling.h (ClangTool)
        - clang/Frontend/FrontendAction.h
        - CppToCFrontendAction (creates ASTConsumer)
      </dependencies>
      <current_location>
        - main.cpp: ClangTool creation and invocation (lines 427-454)
        - CppToCFrontendAction.cpp: FrontendAction implementation
      </current_location>
      <problems>
        - Tightly coupled: ClangTool → FrontendAction → ASTConsumer all created inline
        - Not reusable: ClangTool created in main.cpp, not accessible to tests
        - Hidden dependency: FrontendAction uses extern getSourceDir() from main.cpp
        - Global state: g_filesGeneratedCount shared between main.cpp and ASTConsumer
      </problems>
    </stage>

    <stage name="Dispatcher Transformer">
      <input>
        - C++ ASTContext and TranslationUnitDecl (from Clang parser)
        - TargetContext singleton (shared C ASTContext)
        - PathMapper singleton (source → target mapping)
        - Configuration (via extern accessor functions)
      </input>
      <process>
        - Create all mappers (DeclLocationMapper, DeclMapper, TypeMapper, ExprMapper, StmtMapper)
        - Create CppToCVisitorDispatcher with mapper dependencies
        - Register ALL handlers in dependency order (24 handlers)
        - Dispatch on C++ TranslationUnitDecl
        - Handlers recursively transform C++ AST → C AST
        - C nodes added to C_TranslationUnit via PathMapper
      </process>
      <output>
        - C AST nodes in shared C ASTContext
        - One C_TranslationUnit per output file (managed by PathMapper)
        - Populated mapper tables (C++ node → C node mappings)
        - Updated TargetContext global maps (ctorMap, methodMap, dtorMap)
      </output>
      <side_effects>
        - Mutates TargetContext (adds C nodes, updates maps)
        - Mutates PathMapper (adds C_TU instances, updates caches)
        - Mutates all mappers (adds C++ → C mappings)
        - Logs debug output to llvm::outs()
      </side_effects>
      <dependencies>
        - TargetContext (singleton, global state)
        - PathMapper (singleton, global state)
        - All 24 handlers (via registerWith calls)
        - CNodeBuilder (creates C AST nodes)
        - Configuration accessors (extern functions)
      </dependencies>
      <current_location>
        - DispatcherConsumer::HandleTranslationUnit() (CppToCFrontendAction.cpp, lines 55-112)
        - TranspilerConsumer::HandleTranslationUnit() (TranspilerAPI.cpp, lines 144-196)
        - Handler implementations (src/dispatch/*.cpp)
      </current_location>
      <problems>
        - Handler registration duplicated (2 places, 24 handlers each)
        - Mapper creation duplicated (2 places)
        - Dispatcher creation inline (not reusable)
        - Tightly coupled to ASTConsumer (can't test dispatcher separately)
        - Hidden dependencies on singletons (TargetContext, PathMapper)
        - Configuration via extern functions (global coupling)
      </problems>
    </stage>

    <stage name="C Code Printer">
      <input>
        - C_TranslationUnit (from PathMapper)
        - Output file paths (header + impl)
        - Configuration (pragma once, output dir, etc.)
      </input>
      <process>
        - Create CodeGenerator instances (header + impl)
        - Generate header:
          - Add include guards or #pragma once
          - Iterate C_TU declarations
          - Print each declaration (signature only, declarationOnly=true)
        - Generate implementation:
          - Add #include for header
          - Iterate C_TU declarations
          - Print each declaration (full body, declarationOnly=false)
        - Write files via FileOutputManager
      </process>
      <output>
        - Two files: .h (header) and .c (implementation)
        - Header: struct definitions, function prototypes
        - Impl: function bodies, static variables
      </output>
      <side_effects>
        - Writes files to disk (via FileOutputManager)
        - Creates directories as needed
        - Increments g_filesGeneratedCount on success
        - Logs output filenames to llvm::outs()
      </side_effects>
      <dependencies>
        - CodeGenerator (code generation from C AST)
        - FileOutputManager (file I/O)
        - IncludeGuardGenerator (header guards)
        - Configuration accessors (shouldUsePragmaOnce, getOutputDir)
      </dependencies>
      <current_location>
        - DispatcherConsumer::HandleTranslationUnit() (CppToCFrontendAction.cpp, lines 113-167)
        - TranspilerConsumer::HandleTranslationUnit() (TranspilerAPI.cpp, lines 198-239)
      </current_location>
      <problems>
        - Code generation logic duplicated (2 places)
        - Tightly coupled to ASTConsumer (can't test separately)
        - File writing mixed with code generation (violates SRP)
        - Different separation strategies (simple vs HeaderSeparator)
        - Global state access (g_filesGeneratedCount)
      </problems>
    </stage>
  </pipeline_boundaries>

  <problems>
    <mixing_concerns>
      **DispatcherConsumer mixes 3 pipeline stages:**
      - Stage 4: Dispatcher transformation (lines 55-112)
      - Stage 5: C code generation (lines 113-147)
      - Stage 5: File I/O (lines 149-167)

      Violates Single Responsibility Principle (SRP).
      Makes testing difficult - can't test dispatcher without file I/O.
      Makes reuse difficult - can't use dispatcher without code generation.

      **TranspilerConsumer also mixes 3 stages:**
      - Stage 4: Dispatcher transformation (lines 144-196)
      - Stage 5: C code generation (lines 198-236)
      - Stage 5: String output (lines 238-239)

      Same problems as DispatcherConsumer.

      **main.cpp mixes 2 stages:**
      - Stage 2: File discovery (lines 282-329, 396-424)
      - Stage 3: C++ AST parsing (lines 427-454)

      File discovery should be separate generator component.
      Should yield file paths to iterator/pipeline.
    </mixing_concerns>

    <hidden_dependencies>
      **Extern function coupling:**
      - CppToCFrontendAction.cpp uses extern getSourceDir(), getOutputDir()
      - Defined in main.cpp (lines 200-202)
      - Not defined in TranspilerAPI.cpp (uses local g_currentOptions)
      - Creates tight coupling between FrontendAction and main.cpp
      - Prevents reuse of FrontendAction in library mode

      **Singleton coupling:**
      - All components depend on TargetContext::getInstance()
      - All components depend on PathMapper::getInstance()
      - Singletons are global state, make testing difficult
      - Hard to reset state between tests
      - Thread-unsafe (not currently a problem, but limits future parallelization)

      **Global variable coupling:**
      - g_filesGeneratedCount shared between main.cpp and ASTConsumer
      - Atomic&lt;int&gt; for thread safety, but still global state
      - Makes testing difficult (need to reset between tests)

      **Handler registration coupling:**
      - ASTConsumer must know ALL handlers
      - Must register them in correct dependency order
      - Duplicated in 2 places (hard to maintain)
      - Adding new handler requires updating both consumers
    </hidden_dependencies>

    <global_state>
      **TargetContext singleton:**
      - ONE instance for entire program lifetime
      - Shared C ASTContext (all files write to it)
      - Global maps: ctorMap, methodMap, dtorMap
      - Global deduplication: globalEnums, globalStructs, globalTypedefs
      - Node location tracking: nodeToLocation map

      Benefits: Enables multi-file coordination, deduplication
      Problems: Global state, hard to reset, not thread-safe

      **PathMapper singleton:**
      - ONE instance for entire program lifetime
      - Caches C_TU instances (fileToTU_ map)
      - Caches declaration targets (declToTarget_ map)
      - Source/output dir configuration

      Benefits: Consistent path mapping, C_TU reuse
      Problems: Global state, hard to reset, not thread-safe

      **llvm::cl::opt globals:**
      - All CLI options are global variables
      - Accessed via extern functions
      - Can't have different configs per test

      Benefits: Simple to use, LLVM standard practice
      Problems: Global state, hard to test different configs

      **g_filesGeneratedCount:**
      - Global counter for success reporting
      - Shared between main.cpp and consumers

      Benefits: Simple success tracking
      Problems: Global state, hard to test
    </global_state>

    <testing_difficulties>
      **Can't test stages in isolation:**
      - Stage 4 (dispatcher) mixed with stage 5 (code gen) in ASTConsumer
      - Can't test dispatcher without running code generator
      - Can't test code generator without running dispatcher
      - Can't test file I/O separately

      **Can't test with different configs:**
      - Configuration is global (llvm::cl::opt variables)
      - All tests share same config
      - Can't test different option combinations easily

      **Hard to reset state between tests:**
      - TargetContext singleton persists across tests
      - PathMapper singleton persists across tests
      - Need explicit reset() methods
      - Forgot to reset? Tests interfere with each other

      **Can't mock dependencies:**
      - Components depend on concrete singletons (not interfaces)
      - Can't inject mock TargetContext for testing
      - Can't inject mock PathMapper for testing
      - Can't inject mock FileOutputManager for testing

      **Handler registration is manual:**
      - Must register all 24 handlers in correct order
      - If forgot one, silent failure (node not translated)
      - No compile-time enforcement
      - No runtime validation
    </testing_difficulties>

    <reusability_issues>
      **File discovery not reusable:**
      - Hardcoded in main.cpp
      - Can't reuse in library mode
      - Can't configure exclusion patterns
      - Can't support explicit file lists

      **Dispatcher not reusable:**
      - Created inline in ASTConsumer
      - Tightly coupled to handler registration
      - Can't create dispatcher without registering all handlers
      - Can't test dispatcher in isolation

      **Code generation not reusable:**
      - Mixed with file I/O in ASTConsumer
      - Can't generate code without writing files (except TranspilerAPI)
      - Different separation strategies (DispatcherConsumer vs TranspilerConsumer)

      **FrontendAction not reusable:**
      - Depends on extern functions from main.cpp
      - Can't use in library mode without duplicating accessor functions
      - Each mode (CLI vs API) needs own FrontendAction
    </reusability_issues>
  </problems>

  <reusable_components>
    <keep_as_is>
      <component name="CLI argument parsing">
        - llvm::cl::opt works well for CLI tool
        - Standard LLVM practice
        - Good error messages
        - Automatic help generation

        Recommendation: Keep for main.cpp, don't try to generalize
      </component>

      <component name="Dispatcher handlers (24 handlers)">
        - Well-designed with SRP
        - Each handler has single responsibility
        - Predicate + visitor pattern is clean
        - Handlers are reusable and composable

        Recommendation: Keep handler implementations as-is
        Improvement: Centralize registration (don't duplicate)
      </component>

      <component name="TargetContext singleton">
        - Necessary for multi-file coordination
        - Provides shared C ASTContext (Clang requirement)
        - Manages global deduplication
        - Manages shared maps (ctorMap, methodMap, dtorMap)

        Recommendation: Keep singleton pattern
        Improvement: Add reset() for testing, document thread-safety
      </component>

      <component name="PathMapper singleton">
        - Necessary for consistent path mapping
        - Manages C_TU instances per output file
        - Caches mappings for performance

        Recommendation: Keep singleton pattern
        Improvement: Add reset() for testing, document thread-safety
      </component>

      <component name="CodeGenerator">
        - Well-designed with SRP
        - Uses Clang's DeclPrinter/StmtPrinter (don't reinvent wheel)
        - Configurable with PrintingPolicy
        - Clean API: printDecl(), printStmt(), printTranslationUnit()

        Recommendation: Keep as-is, works great
      </component>

      <component name="FileOutputManager">
        - Well-designed with SRP
        - Handles only file I/O
        - Preserves directory structure
        - Good error handling

        Recommendation: Keep as-is, works great
      </component>

      <component name="CNodeBuilder">
        - Well-designed for creating C AST nodes
        - Encapsulates Clang AST creation boilerplate
        - Type-safe API

        Recommendation: Keep as-is
      </component>

      <component name="Mappers (DeclMapper, TypeMapper, ExprMapper, StmtMapper)">
        - Template-based NodeMapper&lt;K, V&gt; is reusable
        - Clean API: add(), get(), has()
        - Type-safe

        Recommendation: Keep as-is
      </component>
    </keep_as_is>

    <needs_reorganization>
      <component name="File iteration logic">
        Current: Hardcoded in main.cpp (discoverSourceFiles)

        Problems:
        - Not reusable
        - Hardcoded exclusion patterns
        - Can't support explicit file lists

        Recommendation: Extract to FileDiscovery generator
        - Configurable exclusion patterns
        - Support both directory scanning and explicit lists
        - Yield file paths lazily (generator pattern)
        - Reusable in CLI and library modes
      </component>

      <component name="Clang tooling integration">
        Current: ClangTool created inline in main.cpp

        Problems:
        - Not reusable
        - Tightly coupled to FrontendAction
        - Hidden dependencies on extern functions

        Recommendation: Extract to CppAstParser filter
        - Accept file paths (from FileDiscovery generator)
        - Yield C++ AST per file (to Dispatcher filter)
        - Encapsulate ClangTool setup
        - Accept compilation database as parameter
        - Don't use extern functions (pass config explicitly)
      </component>

      <component name="Pipeline orchestration">
        Current: Scattered across main.cpp and ASTConsumer

        Problems:
        - No clear pipeline structure
        - Mixed concerns (parsing + transformation + generation + I/O)
        - Hard to test individual stages

        Recommendation: Extract to TranspilerPipeline orchestrator
        - Clear 5-stage pipeline: CLI → FileDiscovery → CppAstParser → DispatcherTransformer → CCodePrinter
        - Each stage is separate filter/generator
        - Composable: can test each stage separately
        - Configurable: can replace stages (e.g., string output vs file output)
      </component>

      <component name="Handler registration">
        Current: Duplicated in 2 ASTConsumer implementations

        Problems:
        - Code duplication
        - Error-prone (easy to forget handler or get order wrong)
        - No validation

        Recommendation: Extract to HandlerRegistry
        - Single place to register all handlers
        - Validates registration order (check dependencies)
        - Reusable: dispatcherFactory.createWithAllHandlers()
        - Can create custom registries for testing (subset of handlers)
      </component>

      <component name="ASTConsumer implementations">
        Current: DispatcherConsumer and TranspilerConsumer mix 3 stages

        Problems:
        - Violate SRP (dispatcher + code gen + I/O)
        - Code duplication
        - Hard to test

        Recommendation: Split into 3 components
        - DispatcherFilter: C++ AST → C AST only
        - CodeGeneratorFilter: C AST → C code strings only
        - FileWriter: C code strings → files

        Then compose:
        - CLI mode: DispatcherFilter → CodeGeneratorFilter → FileWriter
        - API mode: DispatcherFilter → CodeGeneratorFilter → StringCollector
      </component>
    </needs_reorganization>
  </reusable_components>

  <confidence>High</confidence>

  <dependencies>
    <required>
      - All 5 pipeline stages must be clearly separated
      - Handler registration must be centralized
      - Dispatcher must be extractable from ASTConsumer
      - Code generation must be extractable from ASTConsumer
    </required>
  </dependencies>

  <open_questions>
    <question>Should we keep singletons (TargetContext, PathMapper) or pass them explicitly?</question>
    <rationale>
      Singletons are convenient but make testing harder. Alternative: pass TargetContext and PathMapper explicitly through pipeline stages.

      Pros of singletons:
      - Simpler API (no need to pass context everywhere)
      - Multi-file coordination works naturally
      - Handlers don't need extra parameters

      Cons of singletons:
      - Global state
      - Hard to test (need reset())
      - Not thread-safe
      - Tight coupling

      Recommendation: Keep singletons for now, add reset() for testing. Consider explicit passing in future refactoring.
    </rationale>

    <question>Should handlers be dynamically registered or statically linked?</question>
    <rationale>
      Current: Dynamic registration (registerWith calls at runtime)
      Alternative: Static initialization (global constructors register handlers)

      Pros of dynamic:
      - Explicit control over registration order
      - Can create custom registries for testing
      - Clear dependency order

      Cons of dynamic:
      - Manual registration in 2 places
      - Easy to forget
      - No compile-time enforcement

      Recommendation: Keep dynamic registration, centralize in HandlerRegistry class
    </rationale>

    <question>Should we use generator pattern for file iteration?</question>
    <rationale>
      Current: Collect all files upfront (vector&lt;string&gt;)
      Alternative: Lazy generator (yield one file at a time)

      Pros of generator:
      - Memory efficient for large projects
      - Can start processing before all files discovered
      - More functional/pipeline style

      Cons of generator:
      - More complex (C++ doesn't have native generators)
      - Need custom iterator or callback pattern

      Recommendation: Start with vector (keep it simple), optimize to generator later if needed
    </rationale>

    <question>Should code generation be file-based or TU-based?</question>
    <rationale>
      Current: TU-based (one C_TU per output file, may contain multiple source files)
      Alternative: File-based (one output per source file)

      The TU-based approach is correct for C (header + impl can be separate TUs).
      File-based would mean "one source file → one .c/.h pair" which is too restrictive.

      Recommendation: Keep TU-based approach, it's more flexible
    </rationale>
  </open_questions>

  <assumptions>
    <assumption>
      Single-threaded transpilation is acceptable for now. Multi-threading would require significant refactoring (thread-safe singletons, concurrent map access, etc.).
    </assumption>

    <assumption>
      All source files are in one directory tree. No support for multiple source roots or external dependencies.
    </assumption>

    <assumption>
      Output directory structure mirrors source directory structure. No support for custom output layouts.
    </assumption>

    <assumption>
      One C++ file is processed at a time (serial). ClangTool handles this internally, we don't parallelize.
    </assumption>

    <assumption>
      TargetContext and PathMapper lifetime = program lifetime. No support for multiple transpilation sessions in same process.
    </assumption>

    <assumption>
      Handler registration order matters (dependencies). No automatic dependency resolution.
    </assumption>
  </assumptions>
</pipeline_research>
