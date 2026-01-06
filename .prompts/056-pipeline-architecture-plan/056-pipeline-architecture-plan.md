# Plan: Pipeline Architecture Redesign

## Objective

Design a clean pipeline architecture for cpptoc using generator/filter pattern, based on research findings from `@.prompts/055-pipeline-architecture-research/pipeline-architecture-research.md`.

Transform the current mixed-concern architecture into 5 clear stages with well-defined interfaces.

## Context

**Research Findings:** `@.prompts/055-pipeline-architecture-research/pipeline-architecture-research.md`

**Current Problems:**
- Pipeline stages mixed together in `DispatcherConsumer`
- File iteration coupled with AST parsing
- Hard to test individual stages
- Not reusable as library components

**Target Pipeline:**
```
CLI Args → File Paths → C++ AST → C AST → .c/.h Files
(parse)   (generate)   (filter)  (filter) (filter)
```

## Requirements

### 1. Design Pipeline Stages

For each stage, design:

**Stage 1: CLI Args Parser**
- Input: `int argc, char* argv[]`
- Output: `struct PipelineConfig { ... }`
- Keep existing CLI parsing, wrap in config struct

**Stage 2: Input File Iterator (Generator)**
- Input: `PipelineConfig` (with source dir, file patterns)
- Output: Generator that yields `std::string` file paths
- Consider: C++20 coroutines? Custom iterator? Callback pattern?

**Stage 3: C++ AST Parser (Filter)**
- Input: File path from generator
- Output: `clang::TranslationUnitDecl*` (C++ AST, one TU per file)
- Isolate Clang tooling invocation
- Keep per-file translation units

**Stage 4: Dispatcher Transformer (Filter)**
- Input: `clang::TranslationUnitDecl*` (C++ AST)
- Output: Shared C AST via `TargetContext`
- Use existing `CppToCVisitorDispatcher`
- Accumulate into single shared C AST

**Stage 5: C Code Printer (Filter)**
- Input: Shared C AST from `TargetContext`
- Output: `.c` and `.h` files on disk
- Use existing `CodeGenerator` + `FileOutputManager`

### 2. Design Component Interfaces

Define clean interfaces:

```cpp
// Stage 1: Config
struct PipelineConfig {
    std::string sourceDir;
    std::string outputDir;
    std::vector<std::string> inputFiles;
    // ... other CLI options
};

PipelineConfig parseCLIArgs(int argc, char* argv[]);

// Stage 2: File Iterator (generator pattern)
class FileIterator {
public:
    FileIterator(const PipelineConfig& config);
    std::optional<std::string> next();  // or use C++20 coroutine
};

// Stage 3: C++ AST Parser
class CppASTParser {
public:
    clang::TranslationUnitDecl* parse(const std::string& filePath);
};

// Stage 4: Dispatcher Transformer
class DispatcherTransformer {
public:
    void transform(clang::TranslationUnitDecl* cppAST);
    // Accumulates into TargetContext singleton
};

// Stage 5: C Code Printer
class CCodePrinter {
public:
    void print(TargetContext& targetCtx, const PipelineConfig& config);
};

// Pipeline Orchestrator
class Pipeline {
public:
    void run(const PipelineConfig& config);
};
```

### 3. Plan Migration Strategy

**Phase 1: Extract Stages (no behavior change)**
- Extract `PipelineConfig` struct from CLI parsing
- Extract `FileIterator` from main.cpp file discovery
- Extract `CppASTParser` from `CppToCFrontendAction`/`DispatcherConsumer`
- Extract `DispatcherTransformer` wrapper around existing dispatcher
- Extract `CCodePrinter` wrapper around `CodeGenerator`

**Phase 2: Create Pipeline Orchestrator**
- Create `Pipeline` class that connects stages
- Wire up generator → filter → filter → filter flow
- Keep existing entry points (`main.cpp`, `TranspilerAPI.cpp`) as thin wrappers

**Phase 3: Testing**
- Unit test each stage in isolation
- Integration test full pipeline
- Verify behavior matches original

### 4. Handle Edge Cases

**Singleton Management:**
- `TargetContext` - keep as singleton, accessed by `DispatcherTransformer`
- `PathMapper` - keep as singleton, accessed by `DispatcherTransformer`
- Config - pass explicitly through pipeline

**Error Handling:**
- Each stage returns `Result<T, Error>` or throws?
- Pipeline stops on first error?
- Collect all errors and report at end?

**Multiple Entry Points:**
- `main.cpp` uses CLI → Pipeline
- `TranspilerAPI.cpp` uses API → Config → Pipeline
- Share `Pipeline` implementation

## Output Specification

Save plan to: `.prompts/056-pipeline-architecture-plan/pipeline-architecture-plan.md`

Use this XML structure:

```xml
<pipeline_plan>
  <stage_designs>
    <stage number="1" name="CLI Args Parser">
      <interface>...</interface>
      <implementation_notes>...</implementation_notes>
      <files_affected>...</files_affected>
    </stage>
    <!-- Repeat for all 5 stages -->
  </stage_designs>

  <component_interfaces>
    <header_file name="include/pipeline/PipelineConfig.h">
      <code>...</code>
    </header_file>
    <header_file name="include/pipeline/FileIterator.h">...</header_file>
    <!-- All new headers -->
  </component_interfaces>

  <migration_strategy>
    <phase number="1">
      <description>Extract stages without behavior change</description>
      <steps>
        <step>Extract PipelineConfig</step>
        <step>Extract FileIterator</step>
        <!-- All steps -->
      </steps>
    </phase>
    <phase number="2">...</phase>
    <phase number="3">...</phase>
  </migration_strategy>

  <edge_cases>
    <singleton_management>...</singleton_management>
    <error_handling>...</error_handling>
    <multiple_entry_points>...</multiple_entry_points>
  </edge_cases>

  <confidence>High/Medium/Low</confidence>
  <dependencies>
    <required>Research findings from 055-pipeline-architecture-research</required>
  </dependencies>
  <open_questions>
    <question>Generator pattern: C++20 coroutines vs custom iterator?</question>
    <question>Error handling: exceptions vs Result types?</question>
  </open_questions>
  <assumptions>
    <assumption>Keep singletons (TargetContext, PathMapper) as-is</assumption>
    <assumption>No behavior changes in Phase 1</assumption>
  </assumptions>
</pipeline_plan>
```

### Create SUMMARY.md

Create `.prompts/056-pipeline-architecture-plan/SUMMARY.md` with:

```markdown
# Pipeline Architecture Plan Summary

**5-stage pipeline with generator/filter pattern: Config → Files → C++ AST → C AST → .c/.h**

## Key Decisions
• Stage interfaces: PipelineConfig, FileIterator, CppASTParser, DispatcherTransformer, CCodePrinter
• Generator pattern: Custom iterator (simpler than C++20 coroutines)
• Error handling: Exceptions for now (can refactor to Result<T, E> later)
• Migration: 3 phases (extract, orchestrate, test)

## Decisions Needed
• Approve stage interface designs?
• Approve migration strategy (3 phases)?

## Blockers
None

## Next Step
Create implementation prompt for Phase 1 (extract stages)
```

## Success Criteria

- ✅ All 5 pipeline stages designed with clear interfaces
- ✅ Component interfaces defined (PipelineConfig, FileIterator, etc.)
- ✅ Migration strategy documented (3 phases with detailed steps)
- ✅ Edge cases handled (singletons, errors, multiple entry points)
- ✅ SUMMARY.md created with key decisions
- ✅ Confidence, dependencies, open questions, assumptions included
- ✅ References research findings from previous prompt
