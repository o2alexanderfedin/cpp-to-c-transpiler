<objective>
Execute the complete test suite for work-items-project scripts with comprehensive coverage analysis. This validates the recent auto-initialization implementation and ensures all existing functionality remains intact while identifying any gaps in test coverage.
</objective>

<context>
The work-items-project script library at `~/.claude/skills/lib/work-items-project/` now includes:
- Auto-initialization feature (recently implemented)
- 45+ work item scripts (story, epic, bug, task operations)
- Test suite in `tests/` directory using BATS (Bash Automated Testing System)

This test run will verify:
- All 26 auto-init tests pass (100% coverage target)
- Existing script functionality remains unbroken (backward compatibility)
- Overall code coverage across the entire script library
</context>

<requirements>
1. **Locate all test files** in `~/.claude/skills/lib/work-items-project/tests/`
2. **Execute all BATS test suites** systematically
3. **Capture detailed results** including:
   - Total tests run
   - Pass/fail counts
   - Any failing tests with error messages
   - Execution time
4. **Analyze code coverage**:
   - Which functions are tested
   - Which functions lack tests
   - Coverage percentage for critical files (especially `gh-project-common.sh`)
5. **Identify gaps** where tests are missing or insufficient
</requirements>

<execution_steps>
1. Change directory to the work-items-project root: `~/.claude/skills/lib/work-items-project/`
2. List all test files: `find tests/ -name "*.bats" -o -name "*_test.sh"`
3. For each test file:
   - Run: `bats [test-file]` or appropriate test runner
   - Capture output (both stdout and stderr)
   - Note pass/fail status
4. Aggregate results across all test suites
5. Analyze which source files have corresponding tests
6. Calculate coverage metrics
7. Generate summary report
</execution_steps>

<coverage_analysis>
For each main source file, determine:
- Does a test file exist? (`tests/[name]_test.bats` or similar)
- Which functions are covered by tests?
- Which functions lack test coverage?

Priority files for coverage analysis:
- `lib/gh-project-common.sh` - Core library with auto-init functions
- `story-*.sh` - Story operation scripts
- `epic-*.sh` - Epic operation scripts
- Any other script files in the root directory

Use grep/inspection to identify:
- Function definitions in source files
- Test cases that exercise those functions
- Gaps where functions exist but have no tests
</coverage_analysis>

<output>
Create a comprehensive test report at `./test-reports/work-items-coverage-report.md` with:

## Test Execution Summary
- Total test files executed
- Total test cases run
- Pass count / Fail count
- Execution time
- Overall pass rate percentage

## Test Results by Suite
For each test file:
- File name
- Tests run / passed / failed
- Any error messages for failures

## Coverage Analysis
### Functions Tested
List functions that have test coverage

### Functions Missing Tests
List functions that lack test coverage (CRITICAL GAPS)

### Coverage by File
- `gh-project-common.sh`: X% covered (Y/Z functions)
- Other files with coverage metrics

## Recommendations
- Priority areas needing tests
- Suggestions for improving coverage
- Any backward compatibility concerns identified

## Conclusion
Overall assessment of test suite health and readiness
</output>

<verification>
Before completing, verify:
- [ ] All test files were discovered and executed
- [ ] No test execution errors occurred (tests may fail, but runner should work)
- [ ] Coverage analysis includes all major source files
- [ ] Report clearly identifies any failing tests
- [ ] Gaps in coverage are explicitly listed
- [ ] Report is saved to `./test-reports/work-items-coverage-report.md`
</verification>

<success_criteria>
- All test suites execute successfully (runner works)
- Complete visibility into pass/fail status of every test
- Coverage analysis identifies tested vs untested functions
- Clear action items for improving test coverage
- Report is well-formatted and actionable
</success_criteria>
