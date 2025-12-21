# Integrate ACSL Annotators & Create Comprehensive Integration Tests

## Objective

Integrate all implemented ACSL annotator classes into the main transpiler pipeline and create comprehensive integration tests that verify each feature works end-to-end with Frama-C validation.

## Context

**Current State (CRITICAL FINDINGS):**

The transpiler has **9 ACSL annotator classes** fully implemented with unit tests:
1. ✅ `ACSLGenerator` (base class) - 7 tests passing
2. ✅ `ACSLFunctionAnnotator` - 15 tests passing
3. ✅ `ACSLLoopAnnotator` - 12 tests passing
4. ✅ `ACSLClassAnnotator` - 10 tests passing
5. ✅ `ACSLStatementAnnotator` (Phase 1) - 18 tests passing
6. ✅ `ACSLTypeInvariantGenerator` (Phase 2) - 12 tests passing
7. ✅ `ACSLAxiomaticBuilder` (Phase 3) - 12 tests passing
8. ✅ `ACSLGhostCodeInjector` (Phase 4) - 10 tests passing
9. ✅ `ACSLBehaviorAnnotator` (Phase 5) - 15 tests passing

**Total: 111 unit tests passing (100% success rate)**

**PROBLEM: Zero Integration** ❌

Analysis of main transpiler source files reveals:
- ✅ CLI flags exist (`--generate-acsl`, `--acsl-level`, `--acsl-output`) in `src/main.cpp`
- ❌ **No annotator classes are instantiated anywhere**
- ❌ **No annotator methods are called in the transpiler pipeline**
- ❌ **No integration with `CppToCVisitor`, `CppToCConsumer`, or code generation**
- ❌ **No end-to-end tests validating actual ACSL output**
- ❌ **No Frama-C validation tests**

**Summary:** All ACSL features are implemented and tested in isolation, but **completely disconnected** from the main transpiler. Users cannot actually generate ACSL annotations.

## Project Structure

**Location:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/`

**Key Files:**
```
include/
├── ACSLGenerator.h              # Base class
├── ACSLFunctionAnnotator.h      # Function contracts
├── ACSLLoopAnnotator.h          # Loop invariants
├── ACSLClassAnnotator.h         # Class invariants
├── ACSLStatementAnnotator.h     # Assert/assume/check
├── ACSLTypeInvariantGenerator.h # Type invariants
├── ACSLAxiomaticBuilder.h       # Axioms and lemmas
├── ACSLGhostCodeInjector.h      # Ghost variables
└── ACSLBehaviorAnnotator.h      # Function behaviors

src/
├── main.cpp                     # CLI entry point (has ACSL flags)
├── CppToCVisitor.cpp            # Main AST visitor
├── CppToCConsumer.cpp           # AST consumer
├── CodeGenerator.cpp            # Code generation
└── ACSL*.cpp                    # Annotator implementations (ISOLATED)

tests/
├── ACSL*Test.cpp                # Unit tests (111 passing)
└── integration/                 # DOES NOT EXIST - needs creation
```

## Requirements

### Phase 1: Pipeline Integration (CRITICAL)

**Goal:** Wire all ACSL annotators into the main transpiler pipeline

**Tasks:**

1. **Modify `CppToCVisitor.cpp`** to instantiate and use annotators:
   ```cpp
   class CppToCVisitor : public RecursiveASTVisitor<CppToCVisitor> {
   private:
     // Add ACSL annotator instances
     std::unique_ptr<ACSLFunctionAnnotator> m_functionAnnotator;
     std::unique_ptr<ACSLLoopAnnotator> m_loopAnnotator;
     std::unique_ptr<ACSLClassAnnotator> m_classAnnotator;
     std::unique_ptr<ACSLStatementAnnotator> m_statementAnnotator;
     std::unique_ptr<ACSLTypeInvariantGenerator> m_typeInvariantGen;
     std::unique_ptr<ACSLAxiomaticBuilder> m_axiomaticBuilder;
     std::unique_ptr<ACSLGhostCodeInjector> m_ghostInjector;
     std::unique_ptr<ACSLBehaviorAnnotator> m_behaviorAnnotator;

   public:
     // Initialize annotators in constructor based on CLI flags
     CppToCVisitor(/* ... */) {
       if (shouldGenerateACSL()) {
         m_functionAnnotator = std::make_unique<ACSLFunctionAnnotator>(/* ... */);
         m_loopAnnotator = std::make_unique<ACSLLoopAnnotator>(/* ... */);
         // ... initialize all annotators based on getACSLLevel()
       }
     }

     // Call annotators in Visit* methods
     bool VisitFunctionDecl(FunctionDecl *D) {
       // Existing transpilation logic...

       if (shouldGenerateACSL() && m_functionAnnotator) {
         std::string acsl = m_functionAnnotator->generateFunctionContract(D);
         // Emit ACSL based on getACSLOutputMode() (inline vs separate)
       }

       return true;
     }

     bool VisitCXXRecordDecl(CXXRecordDecl *D) {
       // Existing transpilation logic...

       if (shouldGenerateACSL() && m_classAnnotator) {
         std::string acsl = m_classAnnotator->generateClassInvariant(D);
         // Emit ACSL...
       }

       return true;
     }

     // Similar for loops, statements, etc.
   };
   ```

2. **Add ACSL output emission** in code generation:
   ```cpp
   // In CodeGenerator.cpp or appropriate file
   void emitACSL(const std::string& acsl, ACSLOutputMode mode) {
     if (mode == ACSLOutputMode::Inline) {
       // Insert ACSL comments directly in C output
       m_output << "/*@\n" << acsl << "\n*/\n";
     } else {
       // Write to separate .acsl file
       writeToACSLFile(acsl);
     }
   }
   ```

3. **Wire CLI flags to annotator configuration:**
   - Pass `getACSLLevel()` to control annotation verbosity
   - Respect `--acsl-output` mode (inline vs separate files)
   - Ensure `--generate-acsl` gates all ACSL generation

4. **Update build system:**
   - Ensure all ACSL annotator object files link into main executable
   - Verify CMakeLists.txt includes all annotator sources

**Verification:**
- [ ] Run `./cpptoc --generate-acsl test.cpp` produces ACSL annotations
- [ ] Both `--acsl-output=inline` and `--acsl-output=separate` work
- [ ] `--acsl-level=basic` produces minimal annotations
- [ ] `--acsl-level=full` produces comprehensive annotations
- [ ] All 9 annotator classes are instantiated when `--generate-acsl` enabled

---

### Phase 2: Integration Test Suite Creation

**Goal:** Create end-to-end tests validating ACSL generation pipeline

**Directory Structure:**
```
tests/integration/
├── test-programs/              # C++ test programs
│   ├── simple-function.cpp     # Basic function with contracts
│   ├── array-bounds.cpp        # Array access with bounds checks
│   ├── loop-invariant.cpp      # Loop with invariant
│   ├── class-invariant.cpp     # Class with invariants
│   ├── pointer-safety.cpp      # Pointer validity checks
│   ├── ghost-code.cpp          # Ghost variable usage
│   ├── behaviors.cpp           # Multiple function behaviors
│   ├── axiomatics.cpp          # Axiomatic definitions
│   ├── type-invariants.cpp     # Type-level invariants
│   └── complex-algorithm.cpp   # Multi-feature test
├── expected-output/            # Expected ACSL annotations
│   ├── simple-function.acsl
│   ├── array-bounds.acsl
│   └── ...
├── integration_test_runner.cpp # Test harness
└── CMakeLists.txt              # Build config for integration tests
```

**Test Harness Implementation:**
```cpp
// tests/integration/integration_test_runner.cpp
#include <gtest/gtest.h>
#include <filesystem>
#include <fstream>
#include <sstream>

class ACSLIntegrationTest : public ::testing::Test {
protected:
  void SetUp() override {
    m_testDir = std::filesystem::path(__FILE__).parent_path() / "test-programs";
    m_expectedDir = std::filesystem::path(__FILE__).parent_path() / "expected-output";
  }

  std::string runTranspiler(const std::string& inputFile, const std::string& flags) {
    std::string cmd = "./cpptoc " + flags + " " + (m_testDir / inputFile).string();
    // Execute transpiler and capture output
    // Return generated ACSL
  }

  void compareACSL(const std::string& generated, const std::string& expected) {
    // Normalize whitespace
    // Compare ACSL annotations
    // Allow semantic equivalence (not just string equality)
  }

  std::filesystem::path m_testDir;
  std::filesystem::path m_expectedDir;
};

// Test each annotator integration
TEST_F(ACSLIntegrationTest, FunctionContracts) {
  std::string acsl = runTranspiler("simple-function.cpp", "--generate-acsl");
  std::string expected = readFile(m_expectedDir / "simple-function.acsl");
  compareACSL(acsl, expected);
}

TEST_F(ACSLIntegrationTest, LoopInvariants) {
  std::string acsl = runTranspiler("loop-invariant.cpp", "--generate-acsl --acsl-level=full");
  std::string expected = readFile(m_expectedDir / "loop-invariant.acsl");
  compareACSL(acsl, expected);
}

TEST_F(ACSLIntegrationTest, ClassInvariants) {
  std::string acsl = runTranspiler("class-invariant.cpp", "--generate-acsl");
  std::string expected = readFile(m_expectedDir / "class-invariant.acsl");
  compareACSL(acsl, expected);
}

TEST_F(ACSLIntegrationTest, StatementAnnotations) {
  std::string acsl = runTranspiler("pointer-safety.cpp", "--generate-acsl --acsl-level=full");
  // Verify assert/assume/check annotations present
  EXPECT_NE(acsl.find("/*@ assert"), std::string::npos);
}

TEST_F(ACSLIntegrationTest, TypeInvariants) {
  std::string acsl = runTranspiler("type-invariants.cpp", "--generate-acsl");
  // Verify type invariants generated
  EXPECT_NE(acsl.find("/*@ type invariant"), std::string::npos);
}

TEST_F(ACSLIntegrationTest, GhostCode) {
  std::string acsl = runTranspiler("ghost-code.cpp", "--generate-acsl --acsl-level=full");
  // Verify ghost variable declarations
  EXPECT_NE(acsl.find("/*@ ghost"), std::string::npos);
}

TEST_F(ACSLIntegrationTest, Behaviors) {
  std::string acsl = runTranspiler("behaviors.cpp", "--generate-acsl");
  // Verify behavior annotations
  EXPECT_NE(acsl.find("behavior"), std::string::npos);
}

TEST_F(ACSLIntegrationTest, Axiomatics) {
  std::string acsl = runTranspiler("axiomatics.cpp", "--generate-acsl");
  // Verify axiomatic blocks
  EXPECT_NE(acsl.find("/*@ axiomatic"), std::string::npos);
}

TEST_F(ACSLIntegrationTest, OutputModeInline) {
  std::string output = runTranspiler("simple-function.cpp", "--generate-acsl --acsl-output=inline");
  // Verify ACSL is inline in C code
  EXPECT_NE(output.find("/*@"), std::string::npos);
}

TEST_F(ACSLIntegrationTest, OutputModeSeparate) {
  runTranspiler("simple-function.cpp", "--generate-acsl --acsl-output=separate");
  // Verify separate .acsl file created
  EXPECT_TRUE(std::filesystem::exists("simple-function.acsl"));
}

TEST_F(ACSLIntegrationTest, BasicLevel) {
  std::string acsl = runTranspiler("complex-algorithm.cpp", "--generate-acsl --acsl-level=basic");
  // Basic level should have fewer annotations than full
  size_t basicCount = countAnnotations(acsl);

  std::string acslFull = runTranspiler("complex-algorithm.cpp", "--generate-acsl --acsl-level=full");
  size_t fullCount = countAnnotations(acslFull);

  EXPECT_LT(basicCount, fullCount);
}
```

**Test Programs (Examples):**

```cpp
// tests/integration/test-programs/simple-function.cpp
int add(int a, int b) {
  return a + b;
}

// Expected: tests/integration/expected-output/simple-function.acsl
/*@
  requires INT_MIN <= a + b <= INT_MAX;
  ensures \result == a + b;
*/
```

```cpp
// tests/integration/test-programs/array-bounds.cpp
int sum_array(int* arr, int size) {
  int total = 0;
  for (int i = 0; i < size; i++) {
    total += arr[i];
  }
  return total;
}

// Expected ACSL:
/*@
  requires \valid(arr + (0..size-1));
  requires size >= 0;
  ensures \result == \sum(0, size-1, \lambda int j; arr[j]);
*/
/*@
  loop invariant 0 <= i <= size;
  loop invariant total == \sum(0, i-1, \lambda int j; arr[j]);
  loop assigns i, total;
  loop variant size - i;
*/
```

**Verification:**
- [ ] At least 10 integration tests (one per annotator + combined)
- [ ] Tests cover all CLI flag combinations
- [ ] All integration tests pass
- [ ] Test programs represent real-world C++ patterns

---

### Phase 3: Frama-C Validation Tests

**Goal:** Validate generated ACSL annotations with Frama-C toolchain

**Prerequisites:**
- Frama-C 27.0+ installed
- Why3 1.7+ (for WP plugin)
- Alt-Ergo or Z3 SMT solver

**Test Structure:**
```
tests/framac-validation/
├── wp-tests/                    # Weakest Precondition tests (20+)
│   ├── 01-simple-function.cpp
│   ├── 02-pointer-validity.cpp
│   ├── 03-array-bounds.cpp
│   ├── ...
│   └── 20-stl-containers.cpp
├── eva-tests/                   # Evolved Value Analysis tests (15+)
│   ├── 01-constant-prop.cpp
│   ├── 02-range-analysis.cpp
│   └── ...
├── run-framac-wp.sh             # Automation script
├── run-framac-eva.sh            # Automation script
└── CMakeLists.txt
```

**Frama-C WP Validation Script:**
```bash
#!/bin/bash
# tests/framac-validation/run-framac-wp.sh

TEST_DIR="tests/framac-validation/wp-tests"
RESULTS_DIR="tests/framac-validation/wp-results"
mkdir -p "$RESULTS_DIR"

PASSED=0
FAILED=0

for cpp_file in "$TEST_DIR"/*.cpp; do
  basename=$(basename "$cpp_file" .cpp)
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  echo "Testing: $basename"
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  # 1. Transpile C++ to C with ACSL
  ./cpptoc --generate-acsl --acsl-output=inline "$cpp_file" > "$RESULTS_DIR/$basename.c"

  # 2. Run Frama-C WP on generated C code
  frama-c -wp -wp-rte "$RESULTS_DIR/$basename.c" \
    -wp-timeout 60 \
    -wp-prover alt-ergo,z3 \
    > "$RESULTS_DIR/$basename.wp.log" 2>&1

  # 3. Check if all goals were proven
  if grep -q "Proved: [0-9]*/\1" "$RESULTS_DIR/$basename.wp.log"; then
    echo "✅ PASSED: All WP goals proven"
    ((PASSED++))
  else
    echo "❌ FAILED: Some WP goals unproven"
    grep "Proved:" "$RESULTS_DIR/$basename.wp.log"
    ((FAILED++))
  fi

  echo ""
done

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "WP Validation Results"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Passed: $PASSED"
echo "Failed: $FAILED"
echo "Total:  $((PASSED + FAILED))"
echo "Success Rate: $(echo "scale=2; $PASSED * 100 / ($PASSED + $FAILED)" | bc)%"
```

**WP Test Programs (Examples):**
```cpp
// tests/framac-validation/wp-tests/01-simple-function.cpp
int max(int a, int b) {
  if (a > b) return a;
  return b;
}

// Expected WP result: PROVEN
// - Postcondition: result >= a && result >= b
// - Postcondition: result == a || result == b
```

```cpp
// tests/framac-validation/wp-tests/03-array-bounds.cpp
void safe_copy(int* dest, const int* src, int size) {
  for (int i = 0; i < size; i++) {
    dest[i] = src[i];
  }
}

// Expected WP result: PROVEN
// - Precondition: \valid(dest + (0..size-1))
// - Precondition: \valid_read(src + (0..size-1))
// - Loop invariant: 0 <= i <= size
// - Array access bounds: always within valid range
```

**Frama-C EVA Validation:**
```bash
#!/bin/bash
# tests/framac-validation/run-framac-eva.sh

for cpp_file in tests/framac-validation/eva-tests/*.cpp; do
  basename=$(basename "$cpp_file" .cpp)

  # Transpile with ACSL
  ./cpptoc --generate-acsl "$cpp_file" > "eva-results/$basename.c"

  # Run EVA (value analysis)
  frama-c -eva "eva-results/$basename.c" \
    -eva-precision 11 \
    -eva-warn-signed-overflow \
    > "eva-results/$basename.eva.log" 2>&1

  # Check for alarms
  alarm_count=$(grep -c "alarm" "eva-results/$basename.eva.log" || echo 0)

  if [ "$alarm_count" -eq 0 ]; then
    echo "✅ $basename: No alarms (safe)"
  else
    echo "⚠️  $basename: $alarm_count alarms"
  fi
done
```

**Success Criteria:**
- [ ] At least 20 WP validation tests
- [ ] At least 15 EVA validation tests
- [ ] ≥80% WP proof success rate
- [ ] ≥50% reduction in EVA alarms (vs. unannotated code)
- [ ] All Frama-C runs parse ACSL without syntax errors

---

### Phase 4: Performance & Regression Testing

**Goal:** Ensure ACSL generation doesn't degrade transpiler performance

**Benchmark Suite:**
```
tests/benchmarks/
├── small/                       # < 100 LOC (20 programs)
├── medium/                      # 100-1000 LOC (10 programs)
├── large/                       # > 1000 LOC (5 programs)
├── benchmark_runner.cpp         # Automated benchmarking
└── results/
    ├── baseline-v1.17.0.json    # Without ACSL
    └── with-acsl-v2.0.0.json    # With ACSL
```

**Benchmark Harness:**
```cpp
// tests/benchmarks/benchmark_runner.cpp
#include <chrono>
#include <vector>
#include <string>

struct BenchmarkResult {
  std::string program;
  size_t loc;
  std::chrono::milliseconds transpile_time_baseline;
  std::chrono::milliseconds transpile_time_acsl;
  size_t memory_baseline_kb;
  size_t memory_acsl_kb;
  size_t acsl_lines_generated;
};

class BenchmarkRunner {
public:
  std::vector<BenchmarkResult> runAllBenchmarks() {
    std::vector<BenchmarkResult> results;

    for (const auto& program : getTestPrograms()) {
      BenchmarkResult result;
      result.program = program;

      // Baseline (no ACSL)
      auto start = std::chrono::high_resolution_clock::now();
      runTranspiler(program, "");
      auto end = std::chrono::high_resolution_clock::now();
      result.transpile_time_baseline =
        std::chrono::duration_cast<std::chrono::milliseconds>(end - start);

      // With ACSL
      start = std::chrono::high_resolution_clock::now();
      runTranspiler(program, "--generate-acsl --acsl-level=full");
      end = std::chrono::high_resolution_clock::now();
      result.transpile_time_acsl =
        std::chrono::duration_cast<std::chrono::milliseconds>(end - start);

      results.push_back(result);
    }

    return results;
  }

  void printReport(const std::vector<BenchmarkResult>& results) {
    double avgSlowdown = 0.0;

    for (const auto& r : results) {
      double slowdown = (double)r.transpile_time_acsl.count() /
                        r.transpile_time_baseline.count();
      avgSlowdown += slowdown;

      std::cout << r.program << ": "
                << slowdown << "x slowdown ("
                << r.acsl_lines_generated << " ACSL lines)\n";
    }

    avgSlowdown /= results.size();
    std::cout << "\nAverage slowdown: " << avgSlowdown << "x\n";

    if (avgSlowdown > 1.10) {
      std::cerr << "⚠️  WARNING: Performance regression exceeds 10% threshold!\n";
    }
  }
};
```

**Target Thresholds:**
- Transpilation time increase: ≤10% vs. baseline
- Memory usage increase: ≤10% vs. baseline
- ACSL lines overhead: ≤30% of C code lines

**Verification:**
- [ ] All benchmarks run successfully
- [ ] Performance regression within acceptable bounds
- [ ] Memory usage within acceptable bounds
- [ ] Results documented in benchmark report

---

### Phase 5: Documentation & Examples

**Goal:** Document ACSL features with real-world examples

**Documentation Updates:**

1. **README.md:**
```markdown
## ACSL Annotation Generation

The transpiler can automatically generate ACSL (ANSI/ISO C Specification Language) annotations for formal verification with Frama-C.

### Usage

```bash
# Generate ACSL annotations inline
./cpptoc --generate-acsl myfile.cpp > output.c

# Full annotation coverage
./cpptoc --generate-acsl --acsl-level=full myfile.cpp

# Separate ACSL file
./cpptoc --generate-acsl --acsl-output=separate myfile.cpp
```

### Features

- ✅ Function contracts (requires/ensures/assigns)
- ✅ Loop invariants and variants
- ✅ Class invariants
- ✅ Statement annotations (assert/assume/check)
- ✅ Type invariants
- ✅ Axiomatic definitions
- ✅ Ghost code injection
- ✅ Function behaviors

### Frama-C Validation

```bash
# Transpile with ACSL
./cpptoc --generate-acsl myfile.cpp > output.c

# Verify with Frama-C WP
frama-c -wp output.c

# Value analysis with EVA
frama-c -eva output.c
```
```

2. **docs/ACSL-GUIDE.md** (new file):
```markdown
# ACSL Annotation Guide

## Overview
This transpiler generates ACSL annotations compatible with Frama-C 27.0+.

## Annotator Classes
1. **ACSLFunctionAnnotator**: Function contracts
2. **ACSLLoopAnnotator**: Loop invariants
3. **ACSLClassAnnotator**: Class invariants
4. **ACSLStatementAnnotator**: Inline assertions
5. **ACSLTypeInvariantGenerator**: Type-level invariants
6. **ACSLAxiomaticBuilder**: Mathematical properties
7. **ACSLGhostCodeInjector**: Ghost variables
8. **ACSLBehaviorAnnotator**: Conditional contracts

## Examples
[Include 10+ real-world examples with explanations]
```

3. **Example Gallery:**
```
docs/examples/
├── 01-basic-function.cpp/.c        # Simple function contract
├── 02-array-operations.cpp/.c      # Array bounds safety
├── 03-linked-list.cpp/.c           # Memory safety
├── 04-sorting-algorithm.cpp/.c     # Correctness proof
├── 05-binary-search.cpp/.c         # Correctness proof
├── 06-raii-resource.cpp/.c         # Resource management
├── 07-inheritance.cpp/.c           # Class hierarchies
├── 08-template-code.cpp/.c         # Template instantiation
├── 09-pointer-arithmetic.cpp/.c    # Pointer safety
└── 10-complex-algorithm.cpp/.c     # Multi-feature integration
```

**Verification:**
- [ ] README.md updated with ACSL section
- [ ] ACSL-GUIDE.md created with comprehensive documentation
- [ ] At least 10 examples with explanations
- [ ] All examples verified with Frama-C

---

## Success Criteria (Overall)

### Integration
- [x] All 9 ACSL annotator classes integrated into transpiler pipeline
- [x] CLI flags (`--generate-acsl`, `--acsl-level`, `--acsl-output`) functional
- [x] Annotators instantiated and called in visitor/consumer
- [x] ACSL output emitted in both inline and separate modes

### Testing
- [x] At least 10 integration tests (transpiler end-to-end)
- [x] At least 20 Frama-C WP validation tests
- [x] At least 15 Frama-C EVA validation tests
- [x] All integration tests passing
- [x] ≥80% WP proof success rate
- [x] ≥50% EVA alarm reduction vs. unannotated code

### Performance
- [x] Benchmark suite with small/medium/large programs
- [x] Performance regression ≤10% vs. baseline
- [x] Memory usage increase ≤10% vs. baseline
- [x] Documented performance characteristics

### Documentation
- [x] README.md updated with ACSL features
- [x] ACSL-GUIDE.md created
- [x] At least 10 real-world examples
- [x] All examples Frama-C validated

### Quality
- [x] Zero regressions in existing 111 unit tests
- [x] All new tests passing
- [x] All linters passing (zero errors/warnings)
- [x] Code follows project conventions (SOLID, TDD)

---

## Execution Strategy

**Recommended Approach: Sequential with Verification**

1. **Phase 1: Pipeline Integration** (2-3 days)
   - Modify visitor/consumer to wire annotators
   - Test each annotator integration individually
   - Verify CLI flags work correctly

2. **Phase 2: Integration Tests** (2-3 days)
   - Create test infrastructure
   - Write test programs and expected outputs
   - Implement test harness
   - Run all integration tests

3. **Phase 3: Frama-C Validation** (3-4 days)
   - Install Frama-C toolchain
   - Create WP test suite
   - Create EVA test suite
   - Run validation and analyze results

4. **Phase 4: Performance** (1-2 days)
   - Create benchmark suite
   - Run benchmarks
   - Document results
   - Optimize if needed

5. **Phase 5: Documentation** (1-2 days)
   - Update README
   - Create ACSL guide
   - Write examples
   - Validate all examples

**Total Estimated Time: 9-14 days**

---

## Dependencies

### External Tools
- Frama-C 27.0+ with WP and EVA plugins
- Why3 1.7+ (WP backend)
- Alt-Ergo 2.5+ or Z3 4.12+ (SMT solvers)
- GoogleTest (for integration tests)

### Internal Dependencies
- All 9 ACSL annotator implementations (already complete)
- Transpiler core (CppToCVisitor, CodeGenerator, etc.)
- Build system (CMake)

### Install Commands
```bash
# macOS
brew install frama-c why3 alt-ergo z3

# Linux (Ubuntu/Debian)
apt-get install frama-c why3 alt-ergo z3

# Verify installation
frama-c -version
why3 --version
alt-ergo -version
```

---

## Risks & Mitigation

### Risk 1: Low WP Proof Success Rate (High Impact, Medium Probability)
**Mitigation:**
- Start with simple test programs
- Tune annotation heuristics based on WP feedback
- Add more specific preconditions/postconditions
- Use ghost code to aid proof automation
- Document cases where manual hints needed

### Risk 2: Performance Regression (Medium Impact, Medium Probability)
**Mitigation:**
- Profile hot paths
- Implement annotation caching
- Make ACSL generation lazy (on-demand)
- Provide `--acsl-level=basic` for faster transpilation

### Risk 3: Integration Breaks Existing Features (High Impact, Low Probability)
**Mitigation:**
- Run full regression test suite after each integration step
- Test with and without `--generate-acsl` flag
- Ensure backward compatibility (default: ACSL off)

### Risk 4: Frama-C Syntax Errors (Medium Impact, Low Probability)
**Mitigation:**
- Validate ACSL syntax in unit tests
- Test with Frama-C parser early and often
- Follow ACSL 1.17+ specification strictly

---

## Output Specification

### Files to Create/Modify

**Modified:**
- `src/CppToCVisitor.cpp` - Add annotator instantiation and calls
- `src/CppToCConsumer.cpp` - Add ACSL output handling
- `src/CodeGenerator.cpp` - Add ACSL emission methods
- `CMakeLists.txt` - Add integration and validation tests
- `README.md` - Add ACSL documentation section

**Created:**
- `tests/integration/` - Full integration test suite (10+ tests)
- `tests/framac-validation/` - Frama-C validation tests (35+ tests)
- `tests/benchmarks/` - Performance benchmark suite
- `docs/ACSL-GUIDE.md` - Comprehensive ACSL guide
- `docs/examples/` - 10+ real-world examples

### Summary File

`.prompts/036-acsl-integration-testing/SUMMARY.md`

**Structure:**
```markdown
# ACSL Integration & Testing Summary

**All ACSL annotators integrated into transpiler pipeline with comprehensive testing**

## Integration Status
- ✅ All 9 annotator classes wired into pipeline
- ✅ CLI flags functional (`--generate-acsl`, `--acsl-level`, `--acsl-output`)
- ✅ Both inline and separate output modes working

## Test Results
- Integration tests: X/10 passing
- Frama-C WP tests: X/20 passing (XX% proof success)
- Frama-C EVA tests: X/15 passing (XX% alarm reduction)
- Performance regression: X.X% (threshold: 10%)

## Files Modified
- Modified: 5 core transpiler files
- Created: 45+ test files
- Created: 10+ example programs

## Known Issues
[List any discovered issues]

## Next Steps
1. [Based on test results]
2. [Performance optimization if needed]
3. [Documentation refinements]
```

---

## Quality Checklist

Before completing, verify:
- [ ] All annotators called in transpiler pipeline
- [ ] CLI flags control annotator behavior
- [ ] ACSL output generated in both modes
- [ ] All integration tests passing
- [ ] Frama-C WP success rate ≥80%
- [ ] Frama-C EVA alarm reduction ≥50%
- [ ] Performance regression ≤10%
- [ ] All examples Frama-C validated
- [ ] Documentation complete and accurate
- [ ] Zero regressions in existing tests
- [ ] All linters passing

---

## Notes

- This is **CRITICAL WORK** - features are implemented but unusable without integration
- Integration is straightforward - all annotators have clean interfaces
- Test infrastructure setup is the main effort (worth it for validation)
- Frama-C validation provides **objective quality metric** for ACSL generation
- Success means v2.0.0 release with complete, verified ACSL support
