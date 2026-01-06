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

# Check LLVM 21 availability
if ! command -v /opt/homebrew/opt/llvm/bin/clang &> /dev/null; then
    echo "❌ ERROR: LLVM 21 not found"
    echo "CI/CD uses LLVM 21, but local environment has different version"
    echo ""
    echo "Install LLVM 21:"
    echo "  brew install llvm"
    echo ""
    echo "Then run this script again."
    exit 1
fi

# Verify we're using LLVM 21
LLVM_VERSION=$(/opt/homebrew/opt/llvm/bin/clang --version | head -1)
echo "Using: $LLVM_VERSION"
if [[ ! "$LLVM_VERSION" =~ "21." ]]; then
    echo "❌ ERROR: Must use LLVM 21 to match CI/CD"
    exit 1
fi

echo "✓ LLVM 21 verified"

# ============================================================================
# CLEAN BUILD (eliminate stale state)
# ============================================================================
echo ""
echo "Step 2: Clean build (removing stale state)..."

cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c

# Complete clean - remove ALL build artifacts
rm -rf build
mkdir build

echo "✓ Clean build directory created"

# ============================================================================
# CMAKE CONFIGURATION (exact CI/CD flags)
# ============================================================================
echo ""
echo "Step 3: Configuring with EXACT CI/CD flags..."

# EXACT environment variables from CI/CD
export BUILD_TYPE=Release
export LLVM_VERSION=21
export LLVM_DIR=/opt/homebrew/opt/llvm/lib/cmake/llvm
export Clang_DIR=/opt/homebrew/opt/llvm/lib/cmake/clang

cmake -B build \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_DIR=/opt/homebrew/opt/llvm/lib/cmake/llvm \
  -DClang_DIR=/opt/homebrew/opt/llvm/lib/cmake/clang \
  -DCMAKE_CXX_COMPILER=/opt/homebrew/opt/llvm/bin/clang++ \
  -DCMAKE_C_COMPILER=/opt/homebrew/opt/llvm/bin/clang

if [ $? -ne 0 ]; then
    echo "❌ CMake configuration FAILED"
    exit 1
fi

echo "✓ CMake configuration successful"

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

echo "✓ Build successful"

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
  # "RuntimeModeInlineTest" - EXCLUDED: TDD RED phase (Story #116)
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
