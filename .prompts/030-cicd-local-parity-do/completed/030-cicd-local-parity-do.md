# CI/CD Local Parity Enforcement - Do Prompt

## Objective

**Create an exact local replica of the CI/CD build environment and expose ALL test failures with zero possibility of hiding problems.**

**Why this matters CRITICALLY**: There is currently an unacceptable discrepancy between claimed local test results and actual CI/CD failures. This prompt will:
1. Create a script that builds using EXACT CI/CD configuration
2. Use the EXACT LLVM version that CI/CD uses (LLVM 15, not local LLVM 21)
3. Run EVERY test that CI/CD runs
4. Fail loudly and visibly if ANY test fails
5. Fix ALL discovered issues
6. Make it impossible to lie about test results in the future

## Context

### Current Problem
- **CI/CD**: Failing with RuntimeModeInlineTest and possibly others
- **Local claims**: "All tests passing" - **THIS IS FALSE**
- **Root cause**: Different LLVM versions, incomplete test coverage, or dishonest reporting

### Reference
@.prompts/029-cicd-investigation-fix/cicd-investigation-fix.md - Previous CI/CD investigation (incomplete)

### Key Files
- !.github/workflows/ci.yml - AUTHORITATIVE source of what CI/CD does
- !CMakeLists.txt - Build configuration
- !build/ - Local build directory (may have stale state)

## Requirements

### Phase 1: Create Exact CI/CD Replica Script

**CRITICAL**: Script must use IDENTICAL commands, flags, and environment to CI/CD.

1. **Extract EXACT CI/CD configuration**:
   ```bash
   # Read .github/workflows/ci.yml completely
   # Extract:
   # - EXACT LLVM version (currently 15)
   # - EXACT build type (Release)
   # - EXACT cmake flags
   # - EXACT test list (all 72 tests)
   # - EXACT environment variables
   ```

2. **Create `/tmp/cicd_local_replica.sh`** with:
   ```bash
   #!/bin/bash
   # CI/CD Local Replica - EXACT match to GitHub Actions
   #
   # This script replicates the EXACT CI/CD build process locally
   # using the SAME LLVM version, flags, and test suite.
   #
   # CRITICAL: This script will FAIL if any test fails.
   # There is NO WAY to hide failures.

   set -e  # Exit on any error
   set -o pipefail  # Catch errors in pipes

   echo "=========================================="
   echo "CI/CD LOCAL REPLICA"
   echo "Exact match to GitHub Actions workflow"
   echo "=========================================="
   echo ""

   # ============================================================================
   # ENVIRONMENT VALIDATION
   # ============================================================================
   echo "Step 1: Validating environment..."

   # Check LLVM 15 availability
   if ! command -v /opt/homebrew/opt/llvm@15/bin/clang &> /dev/null; then
       echo "❌ ERROR: LLVM 15 not found"
       echo "CI/CD uses LLVM 15, but local environment has different version"
       echo ""
       echo "Install LLVM 15:"
       echo "  brew install llvm@15"
       echo ""
       echo "Then run this script again."
       exit 1
   fi

   # Verify we're using LLVM 15 (not 21)
   LLVM_VERSION=$(/opt/homebrew/opt/llvm@15/bin/clang --version | head -1)
   echo "Using: $LLVM_VERSION"
   if [[ ! "$LLVM_VERSION" =~ "15." ]]; then
       echo "❌ ERROR: Must use LLVM 15 to match CI/CD"
       exit 1
   fi

   # ============================================================================
   # CLEAN BUILD (eliminate stale state)
   # ============================================================================
   echo ""
   echo "Step 2: Clean build (removing stale state)..."

   cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c

   # Complete clean - remove ALL build artifacts
   rm -rf build
   mkdir build

   # ============================================================================
   # CMAKE CONFIGURATION (exact CI/CD flags)
   # ============================================================================
   echo ""
   echo "Step 3: Configuring with EXACT CI/CD flags..."

   # EXACT environment variables from CI/CD
   export BUILD_TYPE=Release
   export LLVM_VERSION=15
   export LLVM_DIR=/opt/homebrew/opt/llvm@15/lib/cmake/llvm
   export Clang_DIR=/opt/homebrew/opt/llvm@15/lib/cmake/clang

   cmake -B build \
     -DCMAKE_BUILD_TYPE=Release \
     -DLLVM_DIR=/opt/homebrew/opt/llvm@15/lib/cmake/llvm \
     -DClang_DIR=/opt/homebrew/opt/llvm@15/lib/cmake/clang \
     -DCMAKE_CXX_COMPILER=/opt/homebrew/opt/llvm@15/bin/clang++ \
     -DCMAKE_C_COMPILER=/opt/homebrew/opt/llvm@15/bin/clang

   if [ $? -ne 0 ]; then
       echo "❌ CMake configuration FAILED"
       exit 1
   fi

   # ============================================================================
   # BUILD (parallel like CI/CD)
   # ============================================================================
   echo ""
   echo "Step 4: Building with parallel jobs..."

   cmake --build build --config Release --parallel $(sysctl -n hw.ncpu)

   if [ $? -ne 0 ]; then
       echo "❌ Build FAILED"
       exit 1
   fi

   # ============================================================================
   # RUN ALL UNIT TESTS (EXACT list from CI/CD)
   # ============================================================================
   echo ""
   echo "Step 5: Running ALL unit tests (exact CI/CD list)..."

   cd build

   # EXACT test list from .github/workflows/ci.yml
   UNIT_TESTS=(
     "CppToCVisitorTest"
     "NameManglerTest"
     "OverloadResolutionTest"
     "TemplateExtractorTest"
     "MonomorphizationTest"
     "STLIntegrationTest"
     "CodeGeneratorTest"
     "HeaderSeparatorTest"
     "IncludeGuardGeneratorTest"
     "ForwardDeclTest"
     "DependencyAnalyzerTest"
     "FileOutputManagerTest"
     "CFGAnalysisTest"
     "FunctionExitDestructorTest"
     "EarlyReturnDestructorTest"
     "NestedScopeDestructorTest"
     "GotoDestructorTest"
     "LoopDestructorTest"
     "RAIIIntegrationTest"
     "InheritanceTest"
     "VirtualMethodAnalyzerTest"
     "VtableGeneratorTest"
     "VptrInjectorTest"
     "OverrideResolverTest"
     "VtableInitializerTest"
     "VirtualCallTranslatorTest"
     "PureVirtualHandlerTest"
     "VirtualDestructorHandlerTest"
     "VirtualFunctionIntegrationTest"
     "MemberInitListTest"
     "ExceptionFrameTest"
     "ActionTableGeneratorTest"
     "TryCatchTransformerTest"
     "ThrowTranslatorTest"
     "CatchHandlerTypeMatchingTest"
     "ExceptionRuntimeTest"
     "ExceptionIntegrationTest"
     "ExceptionThreadSafetyTest"
     "ExceptionPerformanceTest"
     "TypeInfoGeneratorTest"
     "TypeidTranslatorTest"
     "DynamicCastTranslatorTest"
     "HierarchyTraversalTest"
     "DynamicCastCrossCastTest"
     "CrossCastTraversalTest"
     "VirtualBaseDetectionTest"
     "VirtualBaseOffsetTableTest"
     "VTTGeneratorTest"
     "ConstructorSplitterTest"
     "CoroutineDetectorTest"
     "SuspendPointIdentifierTest"
     "StateMachineTransformerTest"
     "PromiseTranslatorTest"
     "ResumeDestroyFunctionTest"
     "FrameAllocationTest"
     "CoroutineIntegrationTest"
     "RuntimeModeInlineTest"  # CRITICAL: This is in CI/CD list
     "RuntimeModeLibraryTest"
     "RuntimeFeatureFlagsTest"
     "SizeOptimizationTest"
     "OperatorOverloadingTest"
     "LambdaTranslatorTest"
     "MoveSemanticTranslatorTest"
     "TypeTraitsTest"
     "MetaprogrammingTest"
     "EdgeCasesTest"
     "ErrorHandlingTest"
     "FeatureInteractionTest"
     "FeatureCombinationTest"
     "UniquePtrTest"
     "SharedPtrTest"
     "SmartPointerRaiiIntegrationTest"
   )

   FAILED_TESTS=()
   PASSED_TESTS=0

   for test in "${UNIT_TESTS[@]}"; do
     if [ -f "./$test" ]; then
       echo -n "Running $test... "

       # Run test and capture output
       if ./"$test" > /tmp/cicd_replica_${test}.log 2>&1; then
         echo "✓ PASSED"
         PASSED_TESTS=$((PASSED_TESTS + 1))
       else
         echo "✗ FAILED"
         FAILED_TESTS+=("$test")

         # Show failure output immediately (no hiding)
         echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
         echo "FAILURE OUTPUT for $test:"
         tail -30 /tmp/cicd_replica_${test}.log
         echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
       fi
     else
       echo "⚠️  $test not found (may not be built)"
       FAILED_TESTS+=("$test (not built)")
     fi
   done

   # ============================================================================
   # RESULTS SUMMARY
   # ============================================================================
   echo ""
   echo "=========================================="
   echo "CI/CD REPLICA TEST RESULTS"
   echo "=========================================="
   echo "Passed: $PASSED_TESTS"
   echo "Failed: ${#FAILED_TESTS[@]}"
   echo ""

   if [ ${#FAILED_TESTS[@]} -ne 0 ]; then
     echo "❌ FAILED TESTS:"
     for test in "${FAILED_TESTS[@]}"; do
       echo "  - $test"
     done
     echo ""
     echo "These failures MATCH what CI/CD sees."
     echo "Logs saved to /tmp/cicd_replica_*.log"
     echo ""
     exit 1
   else
     echo "✅ ALL TESTS PASSED!"
     echo "CI/CD and local are in PERFECT PARITY"
     exit 0
   fi
   ```

3. **Make script executable and save**:
   ```bash
   chmod +x /tmp/cicd_local_replica.sh
   ```

### Phase 2: Run Script and Expose ALL Failures

**CRITICAL**: Do NOT proceed to Phase 3 until you see EXACT failures.

1. **Run the replica script**:
   ```bash
   /tmp/cicd_local_replica.sh 2>&1 | tee /tmp/cicd_replica_output.log
   ```

2. **Document EVERY failure**:
   - Which tests failed
   - Exact error messages
   - Why they failed locally with LLVM 15 but might have been "passing" with LLVM 21
   - Root cause analysis for each

3. **Compare to CI/CD**:
   - Download latest CI/CD logs
   - Verify local failures EXACTLY match CI/CD failures
   - If they don't match, script is wrong - fix it

### Phase 3: Fix ALL Issues

**CRITICAL**: Fix EVERY issue. Zero tolerance for skipping.

For EACH failing test:

1. **Determine root cause**:
   - Is it truly a TDD RED phase test (RuntimeModeInlineTest)?
   - Is it a real bug?
   - Is it LLVM 15 vs 21 difference?
   - Is it missing implementation?

2. **Apply appropriate fix**:

   **For TDD RED phase tests**:
   - Remove from CI/CD test list (with clear comment why)
   - Document in separate file when it should be re-added
   - Create issue/task to complete implementation

   **For real bugs**:
   - Fix the code
   - Verify fix with replica script
   - Ensure fix works in BOTH LLVM 15 and LLVM 21

   **For missing features**:
   - Implement the feature
   - OR remove test from CI/CD if not ready

3. **Verify each fix locally**:
   ```bash
   # After each fix, re-run replica script
   /tmp/cicd_local_replica.sh

   # Must pass before moving to next issue
   ```

### Phase 4: Enforce Future Parity

**CRITICAL**: Make it impossible to lie about test results in future.

1. **Add replica script to repository**:
   ```bash
   cp /tmp/cicd_local_replica.sh ./scripts/test-cicd-local-parity.sh
   chmod +x ./scripts/test-cicd-local-parity.sh

   # Add to git
   git add scripts/test-cicd-local-parity.sh
   ```

2. **Update documentation**:
   Create `docs/TESTING-PARITY.md`:
   ```markdown
   # CI/CD Testing Parity

   ## Critical Requirement

   Before claiming "all tests pass locally", you MUST run:

   ```bash
   ./scripts/test-cicd-local-parity.sh
   ```

   This script:
   - Uses EXACT LLVM version as CI/CD (15, not 21)
   - Runs EXACT same tests as CI/CD
   - Fails if ANY test fails
   - Cannot hide failures

   ## Why This Exists

   Previously, there were discrepancies between local and CI/CD results due to:
   - Different LLVM versions (21 locally vs 15 in CI)
   - Incomplete test coverage locally
   - Claiming success without running all tests

   This script eliminates all excuses.

   ## Usage

   ### Before any release:
   ```bash
   ./scripts/test-cicd-local-parity.sh
   ```

   ### If it fails:
   1. Read the failure output
   2. Fix ALL failures
   3. Re-run script
   4. Repeat until all pass

   ### Never:
   - Skip failures
   - Claim local tests pass without running this script
   - Use LLVM 21 results as proof of CI/CD readiness
   ```

3. **Add pre-push hook** (optional but recommended):
   ```bash
   cat > .git/hooks/pre-push <<'EOF'
   #!/bin/bash
   # Verify CI/CD parity before pushing to main

   BRANCH=$(git symbolic-ref HEAD 2>/dev/null | cut -d"/" -f 3)

   if [ "$BRANCH" = "main" ] || [[ "$BRANCH" == release/* ]]; then
       echo "🔍 Verifying CI/CD parity before push to $BRANCH..."

       if ! ./scripts/test-cicd-local-parity.sh; then
           echo ""
           echo "❌ CI/CD parity check FAILED"
           echo "Fix all test failures before pushing to $BRANCH"
           exit 1
       fi

       echo "✅ CI/CD parity verified"
   fi
   EOF

   chmod +x .git/hooks/pre-push
   ```

### Phase 5: Commit and Push Fixes

1. **Commit all fixes**:
   ```bash
   git add -A
   git commit -m "fix: enforce CI/CD local parity and fix all test failures

   CRITICAL FIXES:
   - Created scripts/test-cicd-local-parity.sh for exact CI/CD replication
   - Uses LLVM 15 (matching CI/CD) instead of LLVM 21
   - Runs ALL 72 tests that CI/CD runs
   - Fixed [list each test failure here]:
     - RuntimeModeInlineTest: [solution]
     - [other tests]: [solutions]
   - Added TESTING-PARITY.md documentation
   - Added pre-push hook for parity verification

   BEFORE THIS FIX:
   - Claimed local tests passed with LLVM 21
   - CI/CD failed with LLVM 15
   - Discrepancy was hidden

   AFTER THIS FIX:
   - Local testing uses EXACT CI/CD environment
   - ALL failures exposed and fixed
   - Future lying is impossible

   🤖 Generated with [Claude Code](https://claude.com/claude-code)

   Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>"

   git push origin main develop
   ```

2. **Verify CI/CD passes**:
   ```bash
   # Get new run ID
   run_id=$(gh run list --branch main --limit 1 --json databaseId -q '.[0].databaseId')

   # Monitor until completion
   gh run watch $run_id --interval 30
   ```

## Output Specification

### Primary Output
Save detailed report to: `.prompts/030-cicd-local-parity-do/cicd-local-parity.md`

### Output Structure
```xml
<cicd_local_parity>
  <script_created>
    <path>/tmp/cicd_local_replica.sh</path>
    <llvm_version>15</llvm_version>
    <test_count>72</test_count>
    <exact_match_to_cicd>true</exact_match_to_cicd>
  </script_created>

  <initial_run_results>
    <passed>count</passed>
    <failed>count</failed>
    <failures>
      <test name="TestName">
        <error>exact error message</error>
        <root_cause>analysis</root_cause>
      </test>
    </failures>
  </initial_run_results>

  <fixes_applied>
    <fix>
      <test>TestName</test>
      <issue>what was wrong</issue>
      <solution>what was done</solution>
      <verification>how it was verified</verification>
    </fix>
  </fixes_applied>

  <final_verification>
    <local_replica_status>all_pass|some_fail</local_replica_status>
    <cicd_status>all_pass|some_fail</cicd_status>
    <parity_achieved>true|false</parity_achieved>
  </final_verification>

  <enforcement_mechanisms>
    <script_in_repo>scripts/test-cicd-local-parity.sh</script_in_repo>
    <documentation>docs/TESTING-PARITY.md</documentation>
    <pre_push_hook>.git/hooks/pre-push</pre_push_hook>
  </enforcement_mechanisms>

  <metadata>
    <confidence>high - exact CI/CD replication</confidence>
    <remaining_issues>none if successful</remaining_issues>
    <assumptions>listed here</assumptions>
    <next_actions>maintain parity going forward</next_actions>
  </metadata>
</cicd_local_parity>
```

### SUMMARY.md
Create `.prompts/030-cicd-local-parity-do/SUMMARY.md`:

```markdown
# CI/CD Local Parity Enforcement

**One-liner**: [Substantive - e.g., "Created exact CI/CD replica script with LLVM 15, exposed and fixed 3 hidden test failures, achieved perfect parity"]

## Key Findings
- Tests failed locally with LLVM 15: X
- Root cause: [primary causes]
- All failures fixed: Yes/No
- Parity achieved: Yes/No

## Files Created
- `scripts/test-cicd-local-parity.sh` - Exact CI/CD replica
- `docs/TESTING-PARITY.md` - Parity documentation
- `.git/hooks/pre-push` - Pre-push verification hook

## Fixes Applied
- [List each test failure and fix]

## Verification
- ✅ Local replica script passes with LLVM 15
- ✅ CI/CD passes
- ✅ Perfect parity achieved

## Decisions Needed
- [None if successful]

## Blockers
- [None if successful]

## Next Step
- [Maintain parity, use script before all releases]
```

## Success Criteria

### Script Creation Complete When:
- ✅ `/tmp/cicd_local_replica.sh` created
- ✅ Uses EXACT LLVM 15 (not 21)
- ✅ Uses EXACT cmake flags from CI/CD
- ✅ Runs ALL 72 tests from CI/CD
- ✅ Fails loudly if any test fails
- ✅ No way to hide failures

### Initial Run Complete When:
- ✅ Script executed successfully
- ✅ ALL failures documented with exact errors
- ✅ Failures match CI/CD exactly
- ✅ Root causes identified

### Fixes Complete When:
- ✅ EVERY failing test fixed or removed
- ✅ Each fix verified with replica script
- ✅ Script passes with 100% success
- ✅ CI/CD passes with 100% success

### Enforcement Complete When:
- ✅ Script added to repository as `scripts/test-cicd-local-parity.sh`
- ✅ Documentation created as `docs/TESTING-PARITY.md`
- ✅ Pre-push hook installed
- ✅ All committed and pushed

### Documentation Complete When:
- ✅ cicd-local-parity.md created with full XML
- ✅ SUMMARY.md created with substantive one-liner
- ✅ All failures, fixes, and verification documented

## Special Instructions

### Zero Tolerance Policy
- If replica script shows ANY failure, work stops until fixed
- No "mostly passing" or "good enough"
- 100% success or nothing

### Transparency Requirement
- Every failure must be visible in logs
- No suppressing output
- No claiming success without proof

### LLVM Version Discipline
- Use LLVM 15 for CI/CD parity testing
- Use LLVM 21 for development (if needed)
- Never confuse the two
- Always specify which version in reports

### Verification Standard
- Replica script must pass
- CI/CD must pass
- Both must show identical results
- Any discrepancy is a script bug - fix it

## Tools Available

- `cmake`, `make` - Build system
- `/opt/homebrew/opt/llvm@15/` - EXACT CI/CD LLVM version
- `gh` - GitHub CLI for CI/CD monitoring
- `git` - Version control
- All standard bash tools

## Autonomous Execution

You have full autonomy to:
- Create the replica script
- Run it and expose failures
- Fix all issues
- Install enforcement mechanisms
- Commit and push

Do NOT ask permission. Only ask if:
- You discover architectural issues requiring design decisions
- Multiple fix approaches have significant tradeoffs

Otherwise: expose, fix, verify, enforce, document.
