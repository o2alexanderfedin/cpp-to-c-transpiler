# Pipeline Verification Research

## Objective

Verify that the cpptoc transpiler correctly implements all three stages of the C++ to C transpilation pipeline:

1. **Parse C++ to C++ AST** - Using Clang frontend
2. **Transform C++ AST to C AST** - Converting C++ AST nodes to C-compatible AST nodes (same Clang AST, just limited to C subset)
3. **Emit C AST to C code** - Generating .c and .h files from the C AST

This research must determine which stages are fully implemented, which are partially implemented, and which may be missing or incorrectly implemented.

**Why this matters**: The recent Phase 33 baseline showed 0.0% C++23 support. The existing documentation in `tests/real-world/cpp23-validation/README.md` states that "the transpiler currently outputs C++ code with modern C++23 features still present. It does NOT produce valid C99 code." This suggests a potential issue in Stage 2 (C++ AST → C AST transformation) or Stage 3 (C code emission).

## Context

**Reference existing architecture documentation**:
- @docs/ARCHITECTURE.md - Main architecture documentation (if it describes pipeline)
- Recent finding: Phase 33 baseline metrics show 0.0% C++23 support
- Known issue: Transpiler outputs C++ code, not valid C99

**Critical architectural constraint**:
The transpiler does NOT use LLVM IR. It uses only the Clang frontend for parsing. The transformation happens at the AST level, converting C++ AST nodes to C-compatible AST representations.

## Requirements

### Stage 1 Verification: C++ Parsing (Clang Frontend)

**Investigate**:
1. Where is the Clang frontend initialized? (Look for `clang::CompilerInstance`, `clang::ASTConsumer`, `clang::FrontendAction`)
2. What files contain the AST consumption logic?
3. Verify that C++ parsing is delegated to Clang (not custom parser)
4. Check if there are any custom preprocessing steps before Clang parsing

**Key files to examine**:
- !`src/main.cpp` - Entry point
- !`src/CppToCFrontendAction.cpp` - Likely contains Clang integration
- !`include/CppToCConsumer.h` - AST consumer interface
- Any files matching pattern `*FrontendAction*`, `*ASTConsumer*`, `*CompilerInstance*`

**Verification checklist**:
- [ ] Clang frontend is properly initialized
- [ ] C++ AST is successfully parsed
- [ ] AST is accessible for transformation
- [ ] No custom C++ parsing (Clang does it all)

### Stage 2 Verification: C++ AST → C AST Transformation

**This is the critical stage to investigate deeply.**

**Investigate**:
1. Where does AST transformation happen? (Look for visitor pattern, AST node handling)
2. Which C++ AST nodes are transformed to C AST nodes?
3. Are there C++-specific nodes that are NOT being transformed? (namespaces, classes, templates, etc.)
4. How are the following transformed:
   - Classes → Structs with vtables
   - Virtual functions → Function pointers in vtables
   - Templates → Monomorphization (concrete instantiations)
   - Namespaces → Flattened or mangled names
   - Constructors → Init functions
   - Destructors → Cleanup functions
   - Inheritance → Composition
   - Operator overloading → Named functions

**Key files to examine**:
- !`src/CppToCVisitor.cpp` or similar visitor implementation
- !`include/CNodeBuilder.h` - C AST node construction
- !`src/CodeGenerator.cpp` - May contain transformation logic
- Any files with `*Translator*`, `*Handler*`, `*Generator*` patterns
- !Tests in `tests/` directory that validate transformations

**Critical questions**:
- Is the C AST actually constructed, or does the code go straight from C++ AST to text emission?
- Are there separate AST nodes for C output, or is it using Clang's C++ AST nodes?
- How are unsupported C++ features handled (error? warning? passthrough?)

**Verification checklist**:
- [ ] C AST nodes are constructed (not just text generation from C++ AST)
- [ ] Classes are converted to structs
- [ ] Virtual functions are converted to vtables
- [ ] Templates are monomorphized
- [ ] Namespaces are handled (flattened/mangled)
- [ ] Constructors become init functions
- [ ] Destructors become cleanup functions
- [ ] Operator overloading converted to named functions
- [ ] C++23-specific features are either transformed or rejected with errors

**Red flags to watch for**:
- Direct emission of C++ code without transformation
- Passthrough of C++ keywords (class, namespace, template) to output
- No explicit C AST construction
- Transformation happens during emission rather than as separate stage

### Stage 3 Verification: C AST → C Code Emission

**Investigate**:
1. Where is C code emitted? (Look for file writing, code generation)
2. Is emission based on C AST or C++ AST?
3. Are .h and .c files generated separately with proper separation?
4. How are include guards generated?
5. How are forward declarations handled?

**Key files to examine**:
- !`src/CodeGenerator.cpp` - Code emission logic
- !`include/FileOutputManager.h` - File output handling
- !`src/HeaderSeparator.cpp` - Header/implementation separation
- !`include/IncludeGuardGenerator.h` - Include guard generation
- Any files with `*Emitter*`, `*Writer*`, `*Printer*` patterns

**Verification checklist**:
- [ ] C code is emitted (not C++ code)
- [ ] Emission is based on C AST (or C-compatible representation)
- [ ] .h and .c files are properly separated
- [ ] Include guards are generated correctly
- [ ] Forward declarations are handled
- [ ] No C++ keywords appear in emitted code

## Investigation Strategy

### Phase 1: High-Level Architecture Scan (30 minutes)
1. Read @docs/ARCHITECTURE.md if it exists
2. Examine `src/main.cpp` to understand entry point and overall flow
3. Map out the pipeline: Input → Parse → Transform → Emit → Output
4. Identify the key classes/functions for each stage

### Phase 2: Stage 1 Deep Dive (20 minutes)
1. Trace Clang frontend integration
2. Verify C++ AST is properly parsed
3. Document findings with file:line references

### Phase 3: Stage 2 Deep Dive (60 minutes) - **CRITICAL**
1. Find the transformation layer
2. Trace how C++ constructs are converted
3. Check for direct passthrough (RED FLAG)
4. Verify C AST construction exists
5. Test against known failing cases (C++23 features)
6. Document gaps in transformation

### Phase 4: Stage 3 Deep Dive (30 minutes)
1. Trace code emission
2. Verify C output (not C++)
3. Check header/implementation separation
4. Document emission logic

### Phase 5: Gap Analysis (30 minutes)
1. Compare what SHOULD happen vs what DOES happen
2. Identify missing transformations
3. Correlate with Phase 33 baseline failures
4. Prioritize gaps by impact

## Output Specification

Save all findings to: `.prompts/043-pipeline-verification-research/pipeline-verification-research.md`

Use XML structure for machine readability:

```xml
<research>
  <metadata>
    <date>YYYY-MM-DD</date>
    <researcher>Claude Sonnet 4.5</researcher>
    <duration>Estimated time spent</duration>
  </metadata>

  <stage id="1" name="C++ Parsing">
    <status>fully_implemented | partially_implemented | not_implemented</status>
    <key_files>
      <file path="src/main.cpp" lines="10-50">Entry point, initializes Clang</file>
      <!-- More files -->
    </key_files>
    <findings>
      <finding confidence="high">Description of what was found</finding>
      <!-- More findings -->
    </findings>
    <verification_results>
      <item checked="true">Clang frontend properly initialized</item>
      <!-- Checklist items -->
    </verification_results>
  </stage>

  <stage id="2" name="C++ AST to C AST Transformation">
    <status>fully_implemented | partially_implemented | not_implemented</status>
    <key_files>
      <!-- Files involved in transformation -->
    </key_files>
    <findings>
      <finding confidence="high">Description</finding>
    </findings>
    <transformations>
      <transformation from="class" to="struct" status="implemented | partial | missing">
        <details>How it works or what's missing</details>
      </transformation>
      <!-- All transformations -->
    </transformations>
    <gaps>
      <gap severity="critical">Description of missing transformation</gap>
      <!-- More gaps -->
    </gaps>
    <verification_results>
      <!-- Checklist items -->
    </verification_results>
  </stage>

  <stage id="3" name="C Code Emission">
    <status>fully_implemented | partially_implemented | not_implemented</status>
    <key_files>
      <!-- Files for emission -->
    </key_files>
    <findings>
      <finding confidence="high">Description</finding>
    </findings>
    <verification_results>
      <!-- Checklist items -->
    </verification_results>
  </stage>

  <overall_assessment>
    <pipeline_completeness>X%</pipeline_completeness>
    <critical_gaps>
      <gap priority="1">Most urgent issue</gap>
      <!-- More critical gaps -->
    </critical_gaps>
    <correlation_with_phase33>
      How these findings explain the 0.0% C++23 baseline
    </correlation_with_phase33>
  </overall_assessment>

  <confidence>high | medium | low</confidence>
  <dependencies>
    <dependency>What's needed to fix identified gaps</dependency>
  </dependencies>
  <open_questions>
    <question>What remains uncertain</question>
  </open_questions>
  <assumptions>
    <assumption>What was assumed during research</assumption>
  </assumptions>
</research>
```

## Quality Controls

### Verification Checklist
Before submitting research, verify:
- [ ] All three stages traced through codebase
- [ ] File:line references provided for key findings
- [ ] Transformation logic identified (or absence noted)
- [ ] Gaps correlated with Phase 33 baseline failures
- [ ] Confidence levels assigned to all findings
- [ ] Critical claims verified with code evidence

### Sources to Consult
1. **Codebase files** (primary source)
2. **@docs/ARCHITECTURE.md** (if exists)
3. **Test files** in `tests/` directory (show expected behavior)
4. **Phase 33 documentation** at `tests/real-world/cpp23-validation/docs/`
5. **Git history** for recent changes to pipeline components

### QA Questions
Before finalizing:
1. Can I trace the pipeline end-to-end with file:line references?
2. Have I identified WHERE the transformation happens (or should happen)?
3. Can I explain why Phase 33 showed 0.0% C++23 support based on these findings?
4. Have I distinguished between verified facts and assumptions?

### Streaming Write Strategy
To avoid losing work if context runs out:
1. **Write Stage 1 findings immediately** after Phase 2
2. **Write Stage 2 findings immediately** after Phase 3 (most critical)
3. **Write Stage 3 findings immediately** after Phase 4
4. **Update overall_assessment** after Phase 5
5. Use Edit tool to append findings incrementally

## SUMMARY.md Requirement

After completing research, create `.prompts/043-pipeline-verification-research/SUMMARY.md` with:

**One-liner**: Substantive description (e.g., "Stage 2 transformation missing for C++23 features, causing passthrough to output")

**Version**: v1

**Key Findings**:
- Actionable discoveries about each pipeline stage
- Critical gaps identified
- Correlation with Phase 33 failures

**Decisions Needed**:
- What requires user/architect input

**Blockers**:
- External impediments (if any)

**Next Step**:
- Concrete forward action (e.g., "Create plan to implement missing Stage 2 transformations")

## Success Criteria

This research is successful when:
1. All three pipeline stages are mapped with file:line references
2. Transformation logic (or its absence) is identified
3. Gaps are documented with severity levels
4. Phase 33 baseline failures are explained by findings
5. Clear next steps are provided (e.g., "Fix Stage 2 transformation for classes")
6. SUMMARY.md provides executive summary without reading full output
