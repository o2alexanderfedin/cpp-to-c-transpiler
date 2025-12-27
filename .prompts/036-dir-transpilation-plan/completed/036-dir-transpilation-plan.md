# Directory-Based Transpilation Implementation Plan

<objective>
Create implementation plan for directory-based transpilation with source structure preservation.

Purpose: Guide phased implementation from research findings to working feature
Input: dir-transpilation-research.md findings
Output: dir-transpilation-plan.md with implementation phases
</objective>

<context>
Research findings: @.prompts/035-dir-transpilation-research/dir-transpilation-research.md

Key findings to incorporate:
- Recommended path calculation approach from research
- Edge cases identified
- CLI design decisions
- Backward compatibility considerations
</context>

<planning_requirements>
Based on research, create a plan that:
- Implements source directory structure preservation: `source-dir/dir1/dir2/file.cpp` → `target-dir/dir1/dir2/file.c`
- Adds --source-dir CLI option (handle auto-detection per research)
- Maintains backward compatibility with current file-list mode
- Handles edge cases identified in research
- Includes comprehensive testing strategy
- Can be implemented in phases (incremental progress)

Success criteria:
- User can transpile entire project with directory structure preserved
- Backward compatible with existing usage (current tests still pass)
- Edge cases handled gracefully (reject or flatten per research recommendation)
- Well-tested with integration tests
</planning_requirements>

<output_structure>
Save to: `.prompts/036-dir-transpilation-plan/dir-transpilation-plan.md`

Structure the plan using this XML format:

```xml
<plan>
  <summary>
    {One paragraph overview: implement directory-based mode via FileOutputManager enhancement,
     add --source-dir option, preserve structure using std::filesystem::relative(),
     maintain backward compat, X phases over Y estimated effort}
  </summary>

  <phases>
    <phase number="1" name="core-path-calculation">
      <objective>
        Modify FileOutputManager to calculate and preserve relative paths
      </objective>

      <tasks>
        <task priority="high">Add sourceRoot parameter to FileOutputManager constructor</task>
        <task priority="high">Implement calculateRelativePath() private method using std::filesystem::relative()</task>
        <task priority="high">Modify getFullPath() to use relative path instead of basename</task>
        <task priority="high">Add createOutputDirectories() method to ensure parent dirs exist</task>
        <task priority="medium">Handle edge case: files outside source root (per research recommendation)</task>
      </tasks>

      <deliverables>
        <deliverable>FileOutputManager with path preservation capability</deliverable>
        <deliverable>Unit tests for path calculation logic</deliverable>
      </deliverables>

      <dependencies>
        - Research findings on path calculation algorithm
        - Decision on handling files outside source root
      </dependencies>

      <execution_notes>
        Test path calculation separately before integrating.
        Use std::filesystem::relative() per research.
        Handle empty source root (backward compat: use parent of first file).
      </execution_notes>
    </phase>

    <phase number="2" name="cli-integration">
      <objective>
        Add --source-dir CLI option and pass to FileOutputManager
      </objective>

      <tasks>
        <task priority="high">Add --source-dir option to main.cpp (following existing patterns)</task>
        <task priority="high">Add getSourceDir() global accessor</task>
        <task priority="high">Modify CppToCConsumer to pass source dir to FileOutputManager</task>
        <task priority="medium">Implement auto-detection if --source-dir omitted (common ancestor)</task>
        <task priority="low">Update --help text with examples</task>
      </tasks>

      <deliverables>
        <deliverable>Working --source-dir CLI option</deliverable>
        <deliverable>Auto-detection for backward compatibility</deliverable>
      </deliverables>

      <dependencies>
        - Phase 1 complete (FileOutputManager ready)
        - Decision on required vs optional --source-dir
      </dependencies>

      <execution_notes>
        Follow existing CLI option patterns from main.cpp.
        If auto-detect common ancestor, handle single file case.
        Test both explicit and auto-detected source dir.
      </execution_notes>
    </phase>

    <phase number="3" name="testing">
      <objective>
        Create comprehensive tests for directory structure preservation
      </objective>

      <tasks>
        <task priority="high">Add tests to MultiFileTranspilationTest for structure preservation</task>
        <task priority="high">Test nested directories (3+ levels deep)</task>
        <task priority="high">Test with --source-dir explicit</task>
        <task priority="high">Test with auto-detection (no --source-dir)</task>
        <task priority="medium">Test edge case: files outside source root</task>
        <task priority="medium">Test edge case: symlinks in source tree (if relevant per research)</task>
        <task priority="low">Performance test with large directory trees</task>
      </tasks>

      <deliverables>
        <deliverable>8+ new integration tests for dir structure preservation</deliverable>
        <deliverable>Edge case tests with expected behavior documented</deliverable>
      </deliverables>

      <dependencies>
        - Phase 1 and 2 complete
        - Test scenarios from research
      </dependencies>

      <execution_notes>
        Extend existing MultiFileTranspilationTest.cpp.
        Create test directory structures in SetUp().
        Verify output files exist at expected paths.
        Ensure all existing tests still pass (backward compat).
      </execution_notes>
    </phase>

    <phase number="4" name="documentation">
      <objective>
        Update documentation with directory-based usage examples
      </objective>

      <tasks>
        <task priority="high">Update README.md with --source-dir examples</task>
        <task priority="high">Update docs/MULTI_FILE_TRANSPILATION.md with structure preservation section</task>
        <task priority="medium">Add FAQ entry about directory structures</task>
        <task priority="medium">Update transpile_all.sh example script</task>
        <task priority="low">Add architecture diagram showing path calculation flow</task>
      </tasks>

      <deliverables>
        <deliverable>Updated documentation with examples</deliverable>
        <deliverable>Example scripts using --source-dir</deliverable>
      </deliverables>

      <dependencies>
        - Implementation complete and tested
      </dependencies>

      <execution_notes>
        Use real-world example: tests/real-world/ directory.
        Show before/after directory structures.
        Document edge cases and their behavior.
      </execution_notes>
    </phase>
  </phases>

  <metadata>
    <confidence level="high">
      Research identified clear path forward using std::filesystem.
      Modification points are well-defined (FileOutputManager, main.cpp).
      Backward compatibility achieved via auto-detection.
      Testing strategy is comprehensive.
    </confidence>

    <dependencies>
      - C++17 filesystem library (verify in CMakeLists.txt)
      - Decision on required vs optional --source-dir (research suggests optional with auto-detect)
      - Edge case handling decision (research suggests reject files outside source root)
    </dependencies>

    <open_questions>
      - Should we add --flatten option for explicit backward compat mode?
      - Auto-detect: use common ancestor or require at least one parent directory?
      - Should we warn when auto-detecting source root?
    </open_questions>

    <assumptions>
      - Users typically work with source files under a common root
      - std::filesystem::relative() performance is acceptable (very likely)
      - Existing tests verify backward compatibility (MultiFileTranspilationTest exists)
      - Project uses C++17 or later (will verify in Phase 1)
    </assumptions>
  </metadata>
</plan>
```
</output_structure>

<summary_requirements>
Create `.prompts/036-dir-transpilation-plan/SUMMARY.md`:

```markdown
# Directory-Based Transpilation Implementation Plan

**4-phase implementation: core path logic → CLI integration → testing → documentation**

## Phase Breakdown
1. **Core Path Calculation** - FileOutputManager enhancement with std::filesystem::relative()
2. **CLI Integration** - Add --source-dir with auto-detection for backward compat
3. **Testing** - 8+ tests for structure preservation and edge cases
4. **Documentation** - Update all docs with new usage patterns

## Decisions Needed
• Auto-detect source root from common ancestor (recommended) or require explicit --source-dir?
• Reject files outside source root (recommended) or flatten them?

## Blockers
None - research complete, approach is clear

## Next Step
Execute Phase 1: Implement core path calculation in FileOutputManager
```
</summary_requirements>

<success_criteria>
- Plan addresses all requirements (structure preservation, CLI, backward compat, testing)
- Phases are sequential and logical (path calc → integration → test → docs)
- Tasks are specific and actionable
- Edge cases from research are included
- Testing strategy is comprehensive
- Backward compatibility is maintained
- SUMMARY.md created with phase overview
- Ready for implementation
</success_criteria>
