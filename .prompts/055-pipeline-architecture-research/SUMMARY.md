# Pipeline Architecture Research Summary

**Current architecture uses dispatcher pattern with 24 handlers scattered across 2 ASTConsumer implementations (DispatcherConsumer and TranspilerConsumer)**

## Key Findings

### Entry Points
- **main.cpp**: CLI entry with llvm::cl argument parsing, file discovery, and ClangTool invocation
- **TranspilerAPI.cpp**: Library API with in-memory transpilation via runToolOnCodeWithArgs()
- **CppToCFrontendAction.cpp**: Clang FrontendAction that creates DispatcherConsumer inline

### C++ AST Parsing
- **ClangTool** processes multiple files, creating one C++ ASTContext per file
- **FrontendAction::CreateASTConsumer()** called once per file
- **ASTConsumer::HandleTranslationUnit()** receives fully-built C++ AST
- One C++ TranslationUnit per source file (Clang standard)

### Dispatcher Transformation
- **CppToCVisitorDispatcher** with 24 registered handlers (chain of responsibility pattern)
- **Handlers** registered in dependency order: Type/Parameter → Expressions → Statements → Declarations
- **Shared C ASTContext** via TargetContext singleton (all files write to it)
- **One C_TranslationUnit per output file** via PathMapper singleton
- **Mappers** track C++ → C node relationships (DeclMapper, TypeMapper, ExprMapper, StmtMapper)

### C Code Generation
- **CodeGenerator** uses Clang's DeclPrinter/StmtPrinter (don't reinvent wheel)
- **FileOutputManager** handles file I/O with directory structure preservation
- **Two output modes**: File-based (DispatcherConsumer) vs String-based (TranspilerConsumer)

### Pipeline Stages (Current)
1. **CLI Args Parser**: llvm::cl options → parsed config
2. **Input File Iterator**: source dir → vector of file paths (hardcoded in main.cpp)
3. **C++ AST Parser**: file paths → C++ AST per file (ClangTool + FrontendAction)
4. **Dispatcher Transformer**: C++ AST → C AST (CppToCVisitorDispatcher + 24 handlers)
5. **C Code Printer**: C AST → .c/.h files (CodeGenerator + FileOutputManager)

## Current Problems

### 1. Mixing Concerns (Violates SRP)
- **ASTConsumer mixes 3 stages**: Dispatcher transformation + code generation + file I/O
- Both DispatcherConsumer and TranspilerConsumer have identical structure but duplicate code
- Can't test dispatcher without code generation
- Can't test code generation without file I/O

### 2. Code Duplication
- **Handler registration duplicated** in 2 places (24 handlers each)
- **Mapper creation duplicated** in 2 places
- **Code generation logic duplicated** with different separation strategies

### 3. Hidden Dependencies
- **Extern function coupling**: FrontendAction uses `extern getSourceDir()` from main.cpp
- **Singleton coupling**: All components depend on TargetContext::getInstance() and PathMapper::getInstance()
- **Global variable**: g_filesGeneratedCount shared between main.cpp and ASTConsumer

### 4. Global State
- **TargetContext singleton**: Shared C ASTContext, global maps, deduplication
- **PathMapper singleton**: C_TU cache, declaration targets
- **llvm::cl::opt globals**: All CLI options are global variables
- Hard to reset between tests, not thread-safe

### 5. Testing Difficulties
- Can't test stages in isolation (mixed together in ASTConsumer)
- Can't test with different configs (global state)
- Hard to reset state between tests (singletons persist)
- Can't mock dependencies (concrete singletons, not interfaces)

### 6. Reusability Issues
- File discovery hardcoded in main.cpp (can't reuse in library mode)
- Dispatcher created inline (can't test separately)
- Code generation mixed with file I/O (can't reuse for string output easily)

## Components Assessment

### Keep As-Is (Well-Designed)
- ✅ **24 Dispatcher Handlers**: Well-designed with SRP, reusable, composable
- ✅ **TargetContext singleton**: Necessary for multi-file coordination
- ✅ **PathMapper singleton**: Necessary for consistent path mapping
- ✅ **CodeGenerator**: Well-designed, uses Clang's printers
- ✅ **FileOutputManager**: Well-designed, handles only file I/O
- ✅ **CNodeBuilder**: Well-designed for C AST creation
- ✅ **Mappers**: Template-based, type-safe, reusable
- ✅ **CLI argument parsing**: Standard LLVM practice, works well

### Needs Reorganization
- ❌ **File iteration logic**: Extract to FileDiscovery generator (configurable, reusable)
- ❌ **Clang tooling integration**: Extract to CppAstParser filter (accept file paths, yield C++ AST)
- ❌ **Pipeline orchestration**: Extract to TranspilerPipeline (clear 5-stage structure)
- ❌ **Handler registration**: Centralize in HandlerRegistry (single source of truth)
- ❌ **ASTConsumer implementations**: Split into DispatcherFilter + CodeGeneratorFilter + FileWriter

## Decisions Needed

### 1. Singleton vs Explicit Passing
**Question**: Keep TargetContext and PathMapper as singletons, or pass them explicitly through pipeline?

**Recommendation**: Keep singletons for now (simpler API, multi-file coordination works naturally). Add reset() for testing. Consider explicit passing in future refactoring if thread-safety becomes important.

### 2. Handler Registration Strategy
**Question**: Dynamic registration (current) vs static initialization (global constructors)?

**Recommendation**: Keep dynamic registration (explicit control over order), but centralize in HandlerRegistry class to avoid duplication.

### 3. File Iteration Pattern
**Question**: Use generator pattern (lazy, one file at a time) vs vector collection (eager, all files upfront)?

**Recommendation**: Start with vector (simpler, C++ standard practice). Optimize to generator later if memory becomes an issue for large projects.

### 4. Code Generation Granularity
**Question**: TU-based (current: one C_TU per output file) vs File-based (one output per source file)?

**Recommendation**: Keep TU-based (more flexible, matches C standard where header + impl are separate TUs).

## Blockers

**None** - All information gathered, ready to proceed with planning phase.

## Next Steps

1. **Create refactoring plan** with generator/filter pipeline pattern
2. **Define interfaces** for each pipeline stage (FileDiscovery, CppAstParser, DispatcherTransformer, CCodePrinter)
3. **Identify extraction strategy**:
   - Extract HandlerRegistry first (low risk, high value)
   - Extract DispatcherFilter from ASTConsumer (medium risk, enables testing)
   - Extract FileDiscovery generator (low risk, improves reusability)
   - Extract TranspilerPipeline orchestrator (high risk, but biggest benefit)
4. **Plan incremental migration**:
   - Keep old code working while building new pipeline
   - Switch over when new pipeline passes all tests
   - Remove old code in final step

## Success Metrics

- ✅ Each pipeline stage testable in isolation
- ✅ No code duplication (handler registration, mapper creation, code generation)
- ✅ Clear dependencies (no hidden extern functions or global state access)
- ✅ Reusable components (file discovery, dispatcher, code generator)
- ✅ 100% test pass rate maintained throughout refactoring
