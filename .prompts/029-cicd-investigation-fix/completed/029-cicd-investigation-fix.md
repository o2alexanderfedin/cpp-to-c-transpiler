# CI/CD Investigation and Fix - Do Prompt

## Objective

Investigate the current CI/CD pipeline run, identify **ALL** errors and problems, and fix them completely. This is a critical execution task to ensure the release pipeline completes successfully.

**Why this matters**: Release v1.16.3 was just pushed and CI/CD is running. The pipeline must complete successfully to validate the release and ensure all tests pass in the CI environment.

## Context

### Current State
- **Release**: v1.16.3 just created and pushed
- **CI/CD Run**: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/actions/runs/20356140652
- **Status**: Still running after 10+ minutes (expected timeout was hit during local monitoring)
- **Branch**: main (release branches trigger full build)

### Recent Changes (v1.16.3)
- LLVM 15 compatibility fixes (DeclTemplate.h includes, coroutine noexcept)
- Build optimization with shared library pattern (cpptoc_core)
- CI/CD restricted to release branches only
- Added ccache support
- Comprehensive local testing completed (64/64 core tests passing)

### Key Files
- !.github/workflows/ci.yml - CI/CD workflow configuration
- !CMakeLists.txt - Build configuration with shared library
- !tests/ - Test files (coroutine tests modified)

## Requirements

### Phase 1: Investigation (COMPREHENSIVE)

1. **Check CI/CD status and logs**:
   ```bash
   # Get current run status
   gh run view 20356140652 --json status,conclusion,displayTitle,createdAt,updatedAt

   # Get ALL jobs and their status
   gh run view 20356140652 --json jobs -q '.jobs[] | {name: .name, status: .status, conclusion: .conclusion, url: .url}'

   # Download logs for ALL jobs (parallel)
   gh run download 20356140652 --dir /tmp/cicd-logs-20356140652
   ```

2. **Analyze EVERY log file systematically**:
   - Read each job log completely
   - Identify ALL errors, warnings, and failures
   - Note line numbers and exact error messages
   - Categorize issues: build errors, test failures, configuration issues, timeouts

3. **Create comprehensive issue inventory**:
   ```xml
   <issue>
     <id>1</id>
     <job>job-name</job>
     <type>build_error|test_failure|timeout|config_issue</type>
     <severity>critical|high|medium|low</severity>
     <error_message>exact error text</error_message>
     <file>affected file path</file>
     <line>line number if applicable</line>
     <root_cause>analysis of why this happened</root_cause>
   </issue>
   ```

4. **Cross-reference with local environment**:
   - Compare CI environment vs local (LLVM versions, OS, build tools)
   - Identify environment-specific issues
   - Check if issues exist locally but were missed

### Phase 2: Root Cause Analysis

For EACH issue identified:

1. **Determine root cause**:
   - Is it a code bug?
   - Is it a configuration issue?
   - Is it an environment difference?
   - Is it a dependency problem?
   - Is it a test assertion issue?

2. **Check if related to recent changes**:
   - Review v1.16.3 changes
   - Identify which commit introduced the issue
   - Determine if fix was incomplete

3. **Assess impact**:
   - Does it block release?
   - Does it affect functionality?
   - Is it a false positive?

### Phase 3: Fix ALL Issues

**CRITICAL**: Do NOT skip any issues. Fix everything, even if it seems minor.

For each issue, apply appropriate fix:

#### Build Errors
- Fix compilation errors in source files
- Update CMakeLists.txt if needed
- Ensure LLVM 15 compatibility
- Fix include paths and dependencies

#### Test Failures
- Fix test code bugs
- Update test assertions if environment-specific
- Ensure tests pass both locally AND in CI
- Fix any data/path issues

#### Configuration Issues
- Update .github/workflows/ci.yml
- Fix timeout values
- Correct build flags
- Update matrix configurations

#### Timeout Issues
- Identify slow tests/builds
- Optimize build process further
- Increase timeout if justified
- Parallelize better

### Phase 4: Verification

1. **Test fixes locally FIRST**:
   ```bash
   # Run comprehensive local tests
   /tmp/run_all_tests.sh

   # Build with same flags as CI
   cmake -B build -DCMAKE_BUILD_TYPE=Release
   cmake --build build --parallel $(nproc)
   ```

2. **Commit and push fixes**:
   ```bash
   git add -A
   git commit -m "fix: resolve CI/CD issues for v1.16.3

   - [List all fixes applied]
   - Verified locally before push

   🤖 Generated with [Claude Code](https://claude.com/claude-code)

   Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>"

   git push origin main develop
   ```

3. **Monitor new CI/CD run**:
   ```bash
   # Get new run ID
   new_run_id=$(gh run list --branch main --limit 1 --json databaseId -q '.[0].databaseId')

   # Watch until completion (15min timeout)
   gh run watch $new_run_id --interval 30
   ```

4. **Verify success**:
   - All jobs green
   - All tests passing
   - Build artifacts created
   - No warnings or errors

## Output Specification

### Primary Output Location
Save detailed analysis to: `.prompts/029-cicd-investigation-fix/cicd-investigation-fix.md`

### Output Structure
```xml
<cicd_investigation>
  <run_info>
    <run_id>20356140652</run_id>
    <status>completed|in_progress|failed</status>
    <conclusion>success|failure|cancelled</conclusion>
    <duration>total runtime</duration>
  </run_info>

  <issues_found>
    <count>total number</count>
    <by_severity>
      <critical>count</critical>
      <high>count</high>
      <medium>count</medium>
      <low>count</low>
    </by_severity>

    <!-- Detailed issue list -->
    <issue id="1">...</issue>
    <issue id="2">...</issue>
  </issues_found>

  <fixes_applied>
    <count>total fixes</count>

    <fix id="1">
      <issue_ref>1</issue_ref>
      <description>what was fixed</description>
      <files_changed>list of files</files_changed>
      <verification>how it was verified</verification>
    </fix>
  </fixes_applied>

  <verification_results>
    <local_tests>
      <passed>count</passed>
      <failed>count</failed>
      <details>test output summary</details>
    </local_tests>

    <ci_rerun>
      <run_id>new run ID</run_id>
      <status>final status</status>
      <conclusion>final conclusion</conclusion>
      <url>github actions URL</url>
    </ci_rerun>
  </verification_results>

  <metadata>
    <confidence>high|medium|low - how confident all issues are fixed</confidence>
    <remaining_issues>any known issues not yet fixed</remaining_issues>
    <assumptions>what was assumed during investigation</assumptions>
    <next_actions>what should happen next</next_actions>
  </metadata>
</cicd_investigation>
```

### SUMMARY.md Requirements

Create `.prompts/029-cicd-investigation-fix/SUMMARY.md` with:

**Format**:
```markdown
# CI/CD Investigation and Fix

**One-liner**: [Substantive description - e.g., "Fixed 8 build errors and 3 test failures, CI/CD now passing"]

## Key Findings
- Total issues found: X
- Critical: X, High: X, Medium: X, Low: X
- Primary root causes: [list top 3 causes]
- All issues resolved: [Yes/No]

## Files Changed
- [List all files modified]
- [Include brief reason for each change]

## Verification
- ✅ All 64 core tests passing locally
- ✅ CI/CD rerun completed successfully
- ✅ No remaining errors or warnings

## Decisions Needed
- [Any user decisions required - should be NONE if all fixed]

## Blockers
- [Any external blockers - should be NONE if successful]

## Next Step
- [Concrete action - e.g., "Monitor CI/CD run 12345" or "Release complete, no action needed"]
```

## Success Criteria

### Investigation Complete When:
- ✅ All CI/CD job logs reviewed
- ✅ Every error and warning documented
- ✅ Root causes identified for all issues
- ✅ Fix strategy determined for each issue

### Fixes Complete When:
- ✅ All code changes made
- ✅ All configuration updates applied
- ✅ All tests passing locally
- ✅ Changes committed and pushed
- ✅ CI/CD rerun triggered

### Verification Complete When:
- ✅ New CI/CD run completed successfully
- ✅ All jobs green
- ✅ No errors or warnings in logs
- ✅ Release v1.16.3 validated

### Documentation Complete When:
- ✅ cicd-investigation-fix.md created with full XML output
- ✅ SUMMARY.md created with substantive one-liner
- ✅ All issues and fixes documented
- ✅ Verification results included

## Special Instructions

### Parallel Tool Usage
When downloading logs or running tests, use parallel execution:
- Download all job logs simultaneously
- Run test suites in parallel where possible
- Use multiple grep/search operations in single message

### Extended Thinking
For complex root cause analysis:
- Use extended thinking to reason through error chains
- Consider multiple potential causes
- Verify assumptions before applying fixes

### Zero Tolerance for Skipped Issues
- If you find 10 issues, fix ALL 10
- If unsure about a fix, investigate deeper - don't skip
- Better to over-fix than under-fix

### Streaming Write for Large Outputs
When writing cicd-investigation-fix.md:
- Use streaming approach to build incrementally
- Write issues as you find them
- Update fixes section as you apply them
- Keeps context manageable for large investigations

### Quality Gate
Before marking complete:
1. Re-read all job logs to ensure nothing missed
2. Verify each fix actually resolves the issue
3. Confirm new CI/CD run is truly green (not just running)
4. Double-check SUMMARY.md is substantive and accurate

## Tools Available

- `gh` - GitHub CLI for run inspection and log download
- `git` - Version control operations
- `cmake`, `make` - Build system
- `grep`, `rg` - Log analysis
- All standard bash tools
- Read/Write/Edit tools for file modifications
- Bash tool for command execution

## Autonomous Execution

You have full autonomy to:
- Download and analyze all logs
- Make code changes
- Update configuration files
- Run tests
- Commit and push fixes
- Trigger new CI/CD runs
- Monitor progress

Do NOT ask for permission at each step. Only ask if you encounter:
- Ambiguous error requiring architectural decision
- Multiple equally valid fix approaches with different tradeoffs
- Risk of data loss or breaking changes

Otherwise, investigate thoroughly, fix completely, verify rigorously, and document everything.
