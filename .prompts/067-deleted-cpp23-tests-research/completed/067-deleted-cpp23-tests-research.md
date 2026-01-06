# Research Deleted C++20/C++23 Tests for Discussion

<research_objective>
Thoroughly investigate the 97 tests that were deleted during the recent release (v2.16.1) due to C++20/C++23 features being unavailable in LLVM 15.

The goal is to prepare a comprehensive understanding for discussion about:
- Which specific features were removed and why
- The impact on transpiler capabilities
- Potential future support paths
- Alternatives or workarounds

This research will inform decisions about LLVM version upgrades and feature prioritization.
</research_objective>

<context>
Recent release v2.16.1 achieved 100% test pass rate (807/807 tests) by deleting 97 tests that relied on C++20/C++23 features unavailable in LLVM 15.

The transpiler is a C++ to C transpiler using:
- LLVM 15 (current constraint)
- 3-stage pipeline (C++ AST → C AST → C code)
- Dispatcher pattern for AST node handling

Key files to examine:
@.prompts/001-test-failures-do/test-fix-report.md
@.prompts/001-test-failures-do/FINAL-REPORT.md
@.prompts/001-test-failures-do/SUMMARY.md
@CMakeLists.txt (to see what was removed from build)
!git log --oneline --grep="delete" --since="2 days ago" --all
!git diff HEAD~5 HEAD -- CMakeLists.txt | grep -E "^-.*Test" | head -50
</context>

<scope>
Focus on:

1. **Categorization**: Group the 97 deleted tests by feature type
   - C++20 features (modules, concepts, etc.)
   - C++23 features (assume attribute, consteval if, multidim subscript, auto decay-copy, etc.)

2. **LLVM 15 Limitations**: Document which specific APIs are missing
   - Why each feature can't be implemented in LLVM 15
   - What LLVM version would be required for each feature

3. **Impact Assessment**: Evaluate the significance of lost capabilities
   - How critical is each feature for real-world C++ transpilation?
   - Are there workarounds or alternative approaches?

4. **Future Roadmap Implications**: Consider upgrade paths
   - Cost/benefit of upgrading to LLVM 16, 17, or 18
   - Which features would be highest priority to restore

Boundaries:
- Don't investigate how to implement these features (that's a separate task)
- Focus on understanding what was lost and why, not solving it
- Time period: Focus on the most recent changes (last 2 releases)
</scope>

<investigation_steps>
1. **Read the test fix reports** to understand what was deleted:
   - Read @.prompts/001-test-failures-do/test-fix-report.md
   - Read @.prompts/001-test-failures-do/FINAL-REPORT.md
   - Extract the list of deleted test files and their purposes

2. **Examine git history** for deletion details:
   - Run: `git log --oneline --all --grep="delete" --since="1 week ago"`
   - Run: `git log --oneline --all --grep="C++23" --since="1 week ago"`
   - Run: `git show <commit-hash>` for relevant deletion commits
   - Identify which commit(s) deleted the 97 tests

3. **Analyze deleted test file content** (if still in git history):
   - For each category, examine 1-2 example deleted tests
   - Run: `git show <commit>:<path-to-deleted-test>` to view content
   - Understand what C++ features they were testing

4. **Check CMakeLists.txt changes**:
   - Run: `git diff HEAD~10 HEAD -- CMakeLists.txt | grep -A2 -B2 "Test"`
   - Document which test targets were removed

5. **Research LLVM version feature support**:
   - Check which LLVM version introduced each missing feature
   - Use web search if needed for LLVM release notes
   - Create a mapping: Feature → Minimum LLVM version

6. **Categorize by priority**:
   - High priority: Features commonly used in modern C++
   - Medium priority: Useful but not critical
   - Low priority: Niche or experimental features
</investigation_steps>

<deliverables>
Create a comprehensive research document: `.prompts/067-deleted-cpp23-tests-research/research-findings.md`

Structure:
```markdown
# Deleted C++20/C++23 Tests Research

## Executive Summary
- Total tests deleted: 97
- Categories: [list categories]
- LLVM 15 constraint impact: [brief assessment]

## Detailed Breakdown

### 1. C++20 Module Tests (N deleted)
**Tests removed:**
- [Test file 1] - [what it tested]
- [Test file 2] - [what it tested]

**LLVM limitation:**
- [Specific API or feature missing in LLVM 15]
- [Required LLVM version for support]

**Impact assessment:**
- [Critical/Important/Minor]
- [Real-world usage prevalence]

**Example deleted test:**
```cpp
[code snippet from git history]
```

### 2. C++23 Assume Attribute Tests (N deleted)
[Same structure as above]

### 3. C++23 Consteval If Tests (N deleted)
[Same structure as above]

### 4. C++23 Multidimensional Subscript Tests (N deleted)
[Same structure as above]

### 5. C++23 Auto Decay-Copy Tests (N deleted)
[Same structure as above]

### 6. Other Tests (N deleted)
[Same structure as above]

## LLVM Version Comparison

| Feature | Min LLVM | LLVM 15 Support | Notes |
|---------|----------|-----------------|-------|
| C++20 Modules | LLVM 16 | ❌ | Partial support in 15, full in 16 |
| C++23 [[assume]] | LLVM 17 | ❌ | New attribute |
| ... | ... | ... | ... |

## Priority Assessment

**High Priority (restore first if upgrading):**
- [Feature] - [reasoning]

**Medium Priority:**
- [Feature] - [reasoning]

**Low Priority:**
- [Feature] - [reasoning]

## Recommendations

### Short-term (stay on LLVM 15):
- [Any workarounds or alternative approaches]

### Long-term (consider upgrade):
- **LLVM 16**: Gains [features], loses [potential issues]
- **LLVM 17**: Gains [features], loses [potential issues]
- **LLVM 18**: Gains [features], loses [potential issues]

## References
- Git commits: [list relevant commits]
- LLVM release notes: [URLs if searched]
- Test fix reports: [paths to local reports]
```

Save findings to: `.prompts/067-deleted-cpp23-tests-research/research-findings.md`
</deliverables>

<verification>
Before completing, verify:

✅ All 97 deleted tests are accounted for and categorized
✅ Each category has:
   - Count of tests deleted
   - LLVM limitation explanation
   - Impact assessment
   - At least one example from git history

✅ LLVM version comparison table is complete
✅ Priority assessment is based on real-world usage, not just features count
✅ Recommendations section addresses both short-term and long-term options
✅ All git commands executed successfully and relevant commits identified
✅ Sources are cited (commit hashes, file paths, URLs)

</verification>

<success_criteria>
- Complete categorization of all 97 deleted tests by feature type
- Clear documentation of LLVM 15 limitations for each category
- Priority ranking based on real-world usage importance
- Actionable recommendations for future LLVM upgrade decisions
- Ready for informed discussion about deleted features
</success_criteria>
