# Implement: Pipeline Architecture (Phase 1)

## Objective

Implement Phase 1 of the pipeline architecture redesign: Extract pipeline stages into separate components without changing behavior. Create clean interfaces that will enable generator/filter composition.

## Context

**Research:** `@.prompts/055-pipeline-architecture-research/pipeline-architecture-research.md`
**Plan:** `@.prompts/056-pipeline-architecture-plan/pipeline-architecture-plan.md`

**Phase 1 Scope:**
Extract stages without changing behavior. Existing entry points (`main.cpp`, `TranspilerAPI.cpp`, `CppToCFrontendAction.cpp`) continue to work exactly as before, but now they use the new pipeline components internally.

**What NOT to change:**
- CLI argument parsing logic (just wrap in `PipelineConfig`)
- Dispatcher transformation logic (just wrap in `DispatcherTransformer`)
- Code generation logic (just wrap in `CCodePrinter`)
- Entry point behavior (main.cpp output must be identical)

## Requirements

### 1. Create PipelineConfig

**File:** `include/pipeline/PipelineConfig.h`

Extract all configuration from CLI args into a struct:

```cpp
#pragma once
#include <string>
#include <vector>

namespace cpptoc {
namespace pipeline {

struct PipelineConfig {
    // Input/Output paths
    std::string sourceDir;
    std::string outputDir;
    std::vector<std::string> inputFiles;

    // Options (extract from existing CLI parsing)
    bool verbose;
    bool generateACSL;
    // ... all other options from main.cpp CLI parsing
};

// Helper: Parse CLI args into config
PipelineConfig parseCLIArgs(int argc, char* argv[]);

}} // namespace cpptoc::pipeline
```

**Implementation:** `src/pipeline/PipelineConfig.cpp`

Move CLI parsing logic from `main.cpp` into `parseCLIArgs()`.

### 2. Create FileIterator

**File:** `include/pipeline/FileIterator.h`

Extract file discovery/iteration into generator pattern:

```cpp
#pragma once
#include "PipelineConfig.h"
#include <optional>
#include <string>

namespace cpptoc {
namespace pipeline {

class FileIterator {
public:
    explicit FileIterator(const PipelineConfig& config);

    // Generator pattern: returns next file path or nullopt when done
    std::optional<std::string> next();

    // Reset to beginning
    void reset();

private:
    const PipelineConfig& config_;
    size_t currentIndex_;
};

}} // namespace cpptoc::pipeline
```

**Implementation:** `src/pipeline/FileIterator.cpp`

Move file discovery logic from `main.cpp` (currently iterates through input files).

### 3. Create CppASTParser

**File:** `include/pipeline/CppASTParser.h`

Extract C++ AST parsing (Clang invocation) into isolated component:

```cpp
#pragma once
#include "PipelineConfig.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include <memory>

namespace cpptoc {
namespace pipeline {

class CppASTParser {
public:
    explicit CppASTParser(const PipelineConfig& config);

    // Parse single file into C++ AST
    // Returns TranslationUnitDecl for the file
    clang::TranslationUnitDecl* parse(const std::string& filePath);

    // Get the ASTContext for the last parsed file
    clang::ASTContext& getASTContext();

private:
    const PipelineConfig& config_;
    // Store ASTUnit to keep AST alive
    std::unique_ptr<clang::ASTUnit> currentAST_;
};

}} // namespace cpptoc::pipeline
```

**Implementation:** `src/pipeline/CppASTParser.cpp`

Extract from `CppToCFrontendAction.cpp` and `DispatcherConsumer`:
- Clang tooling invocation
- AST creation per file
- Translation unit management

### 4. Create DispatcherTransformer

**File:** `include/pipeline/DispatcherTransformer.h`

Wrapper around existing dispatcher that accumulates into shared C AST:

```cpp
#pragma once
#include "PipelineConfig.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"

namespace cpptoc {
namespace pipeline {

class DispatcherTransformer {
public:
    explicit DispatcherTransformer(const PipelineConfig& config);

    // Transform C++ AST to C AST (accumulates in TargetContext)
    void transform(
        clang::ASTContext& cppASTContext,
        clang::TranslationUnitDecl* cppTU,
        const std::string& sourceFilePath
    );

    // Get the shared C AST context
    TargetContext& getTargetContext();

private:
    const PipelineConfig& config_;
    TargetContext& targetCtx_;
    // Dispatcher is created per-file (handlers need fresh mappers)
};

}} // namespace cpptoc::pipeline
```

**Implementation:** `src/pipeline/DispatcherTransformer.cpp`

Extract from `DispatcherConsumer`:
- Dispatcher creation
- Handler registration
- PathMapper setup
- Mapper creation
- Dispatch invocation

### 5. Create CCodePrinter

**File:** `include/pipeline/CCodePrinter.h`

Wrapper around CodeGenerator for printing C AST to files:

```cpp
#pragma once
#include "PipelineConfig.h"
#include "TargetContext.h"

namespace cpptoc {
namespace pipeline {

class CCodePrinter {
public:
    explicit CCodePrinter(const PipelineConfig& config);

    // Print all C AST from TargetContext to .c and .h files
    void print(TargetContext& targetCtx);

private:
    const PipelineConfig& config_;
};

}} // namespace cpptoc::pipeline
```

**Implementation:** `src/pipeline/CCodePrinter.cpp`

Extract from `DispatcherConsumer`:
- CodeGenerator usage
- Header/impl separation
- FileOutputManager usage
- File writing

### 6. Update CMakeLists.txt

Add new pipeline sources to `cpptoc_core`:

```cmake
# Pipeline components (Phase 1 refactoring)
src/pipeline/PipelineConfig.cpp
src/pipeline/FileIterator.cpp
src/pipeline/CppASTParser.cpp
src/pipeline/DispatcherTransformer.cpp
src/pipeline/CCodePrinter.cpp
```

### 7. Update Entry Points (Minimal Changes)

**main.cpp:**
```cpp
// Before: Direct CLI parsing + file iteration + ...
// After: Use pipeline components
PipelineConfig config = parseCLIArgs(argc, argv);
FileIterator files(config);
CppASTParser parser(config);
DispatcherTransformer transformer(config);
CCodePrinter printer(config);

while (auto filePath = files.next()) {
    auto* cppTU = parser.parse(*filePath);
    transformer.transform(parser.getASTContext(), cppTU, *filePath);
}
printer.print(transformer.getTargetContext());
```

**CppToCFrontendAction.cpp:**
```cpp
// Replace inline DispatcherConsumer with pipeline components
// Keep using Clang's ASTConsumer pattern, but delegate to pipeline
```

**TranspilerAPI.cpp:**
```cpp
// Replace inline consumer with pipeline components
```

## Implementation Guidelines

### Extract, Don't Rewrite
- Copy existing logic into new components
- Keep behavior identical
- Refactor interfaces only
- No algorithmic changes

### Test After Each Component
- Build after creating each header/cpp pair
- Verify compilation
- Verify existing tests still pass

### Preserve Singletons
- `TargetContext::getInstance()` - keep as-is
- `PathMapper::getInstance()` - keep as-is
- Pass `PipelineConfig` explicitly

### Error Handling
- Keep existing error handling (exceptions)
- Don't introduce new error handling patterns yet
- Preserve all error messages

## Output Specification

**Files Created:**
- `include/pipeline/PipelineConfig.h` + `src/pipeline/PipelineConfig.cpp`
- `include/pipeline/FileIterator.h` + `src/pipeline/FileIterator.cpp`
- `include/pipeline/CppASTParser.h` + `src/pipeline/CppASTParser.cpp`
- `include/pipeline/DispatcherTransformer.h` + `src/pipeline/DispatcherTransformer.cpp`
- `include/pipeline/CCodePrinter.h` + `src/pipeline/CCodePrinter.cpp`

**Files Modified:**
- `CMakeLists.txt` - add pipeline sources
- `src/main.cpp` - use pipeline components
- `src/CppToCFrontendAction.cpp` - use pipeline components
- `src/TranspilerAPI.cpp` - use pipeline components

### Create SUMMARY.md

Create `.prompts/057-pipeline-implementation/SUMMARY.md`:

```markdown
# Pipeline Implementation (Phase 1) Summary

**Extracted 5 pipeline stages into separate components with clean interfaces**

## Files Created
• include/pipeline/PipelineConfig.h + .cpp
• include/pipeline/FileIterator.h + .cpp
• include/pipeline/CppASTParser.h + .cpp
• include/pipeline/DispatcherTransformer.h + .cpp
• include/pipeline/CCodePrinter.h + .cpp

## Key Changes
• CLI parsing wrapped in PipelineConfig
• File iteration extracted to FileIterator (generator pattern)
• Clang invocation isolated in CppASTParser
• Dispatcher wrapped in DispatcherTransformer
• Code generation wrapped in CCodePrinter

## Decisions Needed
None - behavior unchanged from before

## Blockers
None

## Next Step
Phase 2: Create Pipeline orchestrator to compose stages
```

## Success Criteria

- ✅ All 5 pipeline component headers created
- ✅ All 5 pipeline component implementations created
- ✅ CMakeLists.txt updated with pipeline sources
- ✅ Entry points updated to use pipeline components
- ✅ Project builds successfully
- ✅ Existing tests pass (behavior unchanged)
- ✅ SUMMARY.md created
- ✅ Code follows existing style and conventions
