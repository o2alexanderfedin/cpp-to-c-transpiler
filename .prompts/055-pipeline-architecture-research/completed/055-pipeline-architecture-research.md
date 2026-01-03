# Research: Current cpptoc Architecture for Pipeline Redesign

## Objective

Research and document the current cpptoc program architecture to identify what needs to be reorganized into a clear pipeline with generator/filter pattern. Focus on understanding the existing flow so we can design a clean pipeline architecture.

## Context

**Current State:**
- The cpptoc program has been migrated from monolithic `CppToCVisitor` to dispatcher architecture
- `CppToCConsumer` has been removed
- `CppToCFrontendAction` now creates `DispatcherConsumer` inline
- We have CLI arg parsing, file iteration, C++ AST parsing, dispatcher transformation, and C code generation
- Code is scattered across multiple files without clear pipeline stages

**Target Pipeline (Generator/Filter Pattern):**
1. **CLI Args Parser** → generates configuration
2. **Input File Iterator** → generates file paths (generator)
3. **C++ AST Parser** → transforms file paths to C++ AST (filter, one TU per file)
4. **Dispatcher Transformer** → transforms C++ AST to single shared C AST (filter)
5. **C Code Printer** → transforms C AST to .c/.h files (filter)

## Requirements

### 1. Map Current Architecture

Identify and document:

**Entry Points:**
- `src/main.cpp` - Main CLI entry point
- `src/TranspilerAPI.cpp` - Library API entry point
- Command line parsing logic
- File discovery and iteration logic

**C++ AST Parsing:**
- How files are passed to Clang
- How C++ AST is created (per-file translation units)
- `CppToCFrontendAction` and `DispatcherConsumer` roles
- Where `clang::tooling` is used

**Dispatcher Transformation:**
- `CppToCVisitorDispatcher` usage
- Handler registration
- How C++ AST → C AST transformation happens
- `TargetContext` and shared C AST management
- `PathMapper` for file-to-TU mapping

**C Code Generation:**
- `CodeGenerator` usage
- How C AST is traversed
- `.h` and `.c` file emission
- `FileOutputManager` responsibilities

### 2. Identify Pipeline Boundaries

For each stage, identify:
- **Input**: What data/objects does it consume?
- **Process**: What transformations happen?
- **Output**: What data/objects does it produce?
- **Side Effects**: File I/O, global state, etc.
- **Dependencies**: What other components does it need?

### 3. Analyze Current Problems

Document issues with current architecture:
- **Mixing concerns**: Where are multiple pipeline stages combined?
- **Hidden dependencies**: Implicit coupling between components
- **Global state**: Singletons and shared mutable state
- **Testing difficulties**: What's hard to test in isolation?
- **Reusability**: What can't be easily reused or composed?

### 4. Identify Reusable Components

What can stay as-is:
- CLI argument parsing
- Dispatcher handlers
- `TargetContext` singleton
- `PathMapper` singleton
- `CodeGenerator`
- `FileOutputManager`

What needs reorganization:
- File iteration logic
- Clang tooling integration
- Pipeline orchestration
- Handler registration

## Output Specification

Save research findings to: `.prompts/055-pipeline-architecture-research/pipeline-architecture-research.md`

Use this XML structure:

```xml
<pipeline_research>
  <current_architecture>
    <entry_points>
      <file path="src/main.cpp">
        <responsibilities>...</responsibilities>
        <cli_parsing>...</cli_parsing>
        <file_discovery>...</file_discovery>
      </file>
      <file path="src/TranspilerAPI.cpp">...</file>
      <file path="src/CppToCFrontendAction.cpp">...</file>
    </entry_points>

    <cpp_ast_parsing>
      <clang_tooling_usage>...</clang_tooling_usage>
      <translation_unit_creation>...</translation_unit_creation>
      <ast_consumer_pattern>...</ast_consumer_pattern>
    </cpp_ast_parsing>

    <dispatcher_transformation>
      <handler_registration>...</handler_registration>
      <cpp_to_c_transform>...</cpp_to_c_transform>
      <shared_c_ast>...</shared_c_ast>
    </dispatcher_transformation>

    <c_code_generation>
      <code_generator_usage>...</code_generator_usage>
      <file_emission>...</file_emission>
    </c_code_generation>
  </current_architecture>

  <pipeline_boundaries>
    <stage name="CLI Args Parser">
      <input>...</input>
      <process>...</process>
      <output>...</output>
      <side_effects>...</side_effects>
      <dependencies>...</dependencies>
    </stage>
    <!-- Repeat for all 5 stages -->
  </pipeline_boundaries>

  <problems>
    <mixing_concerns>...</mixing_concerns>
    <hidden_dependencies>...</hidden_dependencies>
    <global_state>...</global_state>
    <testing_difficulties>...</testing_difficulties>
    <reusability_issues>...</reusability_issues>
  </problems>

  <reusable_components>
    <keep_as_is>
      <component name="...">...</component>
    </keep_as_is>
    <needs_reorganization>
      <component name="...">...</component>
    </needs_reorganization>
  </reusable_components>

  <confidence>High/Medium/Low</confidence>
  <dependencies>
    <required>What must exist to proceed with planning</required>
  </dependencies>
  <open_questions>
    <question>What remains unclear</question>
  </open_questions>
  <assumptions>
    <assumption>What was assumed during research</assumption>
  </assumptions>
</pipeline_research>
```

### Create SUMMARY.md

Create `.prompts/055-pipeline-architecture-research/SUMMARY.md` with:

```markdown
# Pipeline Architecture Research Summary

**Current architecture uses [X] pattern with [Y] components scattered across [Z] files**

## Key Findings
• Entry point: main.cpp + TranspilerAPI.cpp (two paths)
• C++ parsing: CppToCFrontendAction + DispatcherConsumer (inline, not reusable)
• Transformation: CppToCVisitorDispatcher + 24 handlers (works well)
• Code gen: CodeGenerator + FileOutputManager (works well)
• Problem: Pipeline stages mixed in DispatcherConsumer, hard to test/reuse

## Decisions Needed
• Use generator pattern for file iteration?
• Keep TargetContext singleton or pass explicitly?
• Single C AST vs per-file C AST management?

## Blockers
None

## Next Step
Create plan for pipeline refactoring with generator/filter pattern
```

## Success Criteria

- ✅ All entry points mapped (main.cpp, TranspilerAPI.cpp, CppToCFrontendAction.cpp)
- ✅ C++ AST parsing flow documented (how Clang is invoked, TU creation)
- ✅ Dispatcher transformation documented (handler registration, C AST creation)
- ✅ C code generation documented (CodeGenerator usage, file writing)
- ✅ Pipeline boundaries identified for all 5 stages
- ✅ Current problems documented (mixing concerns, hidden dependencies)
- ✅ Reusable vs needs-reorganization components identified
- ✅ SUMMARY.md created with actionable findings
- ✅ Confidence, dependencies, open questions, assumptions included
