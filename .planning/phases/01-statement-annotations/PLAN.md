# Phase 1 Plan: Statement Annotations (v1.18.0)

**Phase**: 1 of 7
**Roadmap**: `.planning/ROADMAP.md`
**Brief**: `.planning/BRIEF.md`
**Target Version**: v1.18.0
**Status**: READY

## Phase Goal

Implement ACSL statement annotations (`assert`, `assume`, `check`) to strengthen verification of transpiled C code. Strategically place annotations at safety-critical points (pointer dereferences, array accesses, arithmetic operations) to enable automatic proof of runtime safety properties.

## Context

### Current State (v1.17.0)
- **Function annotations**: Preconditions, postconditions, assigns clauses
- **Loop annotations**: Invariants, variants, assigns
- **Class annotations**: Invariant predicates

### Gap
No statement-level annotations within function bodies. Cannot express intermediate assertions, proof assumptions, or custom proof obligations.

### Why This Phase
Statement annotations are foundational for other phases:
- Phase 2 (Type Invariants) benefits from assertions validating type constraints
- Phase 4 (Ghost Code) uses ghost assertions for proof bookkeeping
- Phase 5 (Behaviors) can include behavior-specific assertions

## Deliverables

### Source Code
- [x] `include/ACSLStatementAnnotator.h` - Header file with class declaration
- [x] `src/ACSLStatementAnnotator.cpp` - Implementation
- [x] Integration with main transpiler pipeline

### Tests
- [x] `tests/ACSLStatementAnnotatorTest.cpp` - Unit test suite (15+ tests)
- [x] Test cases covering all annotation types and placement strategies

### CLI Integration
- [x] Add `--acsl-statements={none,basic,full}` flag
- [x] Update help text and documentation

### Documentation
- [x] Update `docs/CHANGELOG.md` for v1.18.0
- [x] Update `README.md` features list
- [x] Update `website/src/pages/features.astro`

### Release
- [x] Git-flow release v1.18.0
- [x] Tag and push to remote

## Technical Design

### ACSLStatementAnnotator Class

**Responsibilities** (Single Responsibility Principle):
- Traverse function AST to identify annotation points
- Generate appropriate ACSL statement annotations
- Insert annotations at strategic locations

**Interface** (Interface Segregation Principle):
```cpp
class ACSLStatementAnnotator {
public:
  /// @brief Annotate statements within a function
  /// @param func Function to annotate
  /// @param level Annotation verbosity level
  /// @return Annotated source code with statement annotations
  std::string annotateFunction(const clang::FunctionDecl *func,
                                AnnotationLevel level);

private:
  /// @brief Visit statements and generate annotations
  void visitStmt(const clang::Stmt *stmt, AnnotationLevel level);

  /// @brief Generate assert annotation for expression
  std::string generateAssert(const clang::Expr *expr);

  /// @brief Generate assume annotation for expression
  std::string generateAssume(const clang::Expr *expr);

  /// @brief Generate check annotation for expression
  std::string generateCheck(const clang::Expr *expr);

  /// @brief Determine if statement needs annotation
  bool needsAnnotation(const clang::Stmt *stmt, AnnotationLevel level);

  /// @brief Extract safety property from statement
  std::string extractSafetyProperty(const clang::Stmt *stmt);
};
```

### Annotation Placement Strategy

#### Assert Placement (Runtime + Proof)
Generate `//@ assert expr;` for:

1. **Pointer Dereferences**:
   ```cpp
   int *p = getPointer();
   //@ assert \valid(p);
   int x = *p;
   ```

2. **Array Accesses**:
   ```cpp
   int arr[10];
   int idx = getIndex();
   //@ assert 0 <= idx < 10;
   int val = arr[idx];
   ```

3. **Division Operations**:
   ```cpp
   int a = 10, b = getB();
   //@ assert b != 0;
   int result = a / b;
   ```

4. **Dynamic Casts**:
   ```cpp
   Base *base = getBase();
   //@ assert \valid(base);
   Derived *derived = dynamic_cast<Derived*>(base);
   //@ assert derived != \null;
   ```

5. **Buffer Operations**:
   ```cpp
   char buffer[256];
   const char *src = getString();
   //@ assert \valid_read(src + (0..strlen(src)));
   //@ assert strlen(src) < 256;
   strcpy(buffer, src);
   ```

#### Assume Placement (Proof Context)
Generate `//@ assume expr;` for:

1. **Validated Input**:
   ```cpp
   int validate(int input) {
     if (input < 0 || input > 100) return -1;
     //@ assume 0 <= input <= 100;  // Post-validation
     return process(input);
   }
   ```

2. **Constructor Post-Initialization**:
   ```cpp
   MyClass::MyClass(int size) {
     this->size = size;
     this->data = new int[size];
     //@ assume \valid(this->data + (0..size-1));
     //@ assume this->size > 0;
   }
   ```

3. **Platform Assumptions**:
   ```cpp
   void platformSpecific() {
     //@ assume sizeof(int) == 4;
     //@ assume sizeof(void*) == 8;
     // Platform-specific code
   }
   ```

#### Check Placement (Proof Obligations Only)
Generate `//@ check expr;` for:

1. **Proof Milestones**:
   ```cpp
   void complexAlgorithm(int *arr, int n) {
     // Phase 1: partition
     int pivot = partition(arr, n);
     //@ check \forall integer i; 0 <= i < pivot ==> arr[i] <= arr[pivot];

     // Phase 2: sort
     sort(arr, pivot);
     //@ check \forall integer i; 0 <= i < pivot-1 ==> arr[i] <= arr[i+1];
   }
   ```

2. **Invariant Maintenance**:
   ```cpp
   void insert(int val) {
     //@ check isSorted(data, size);  // Invariant before
     insertSorted(val);
     //@ check isSorted(data, size+1);  // Invariant after
   }
   ```

### Verbosity Levels

**None** (`--acsl-statements=none`):
- No statement annotations generated
- Preserves v1.17.0 behavior

**Basic** (`--acsl-statements=basic`):
- Null pointer checks before dereferences
- Division by zero checks
- Array bounds checks (when statically determinable)

**Full** (`--acsl-statements=full`):
- All basic checks
- Buffer overflow checks
- Arithmetic overflow checks
- Type safety checks (casts)
- Custom proof obligations (check annotations)

### Integration Points

#### Main Transpiler Pipeline
```cpp
// In TranspilerMain.cpp
if (options.acslStatements != AnnotationLevel::None) {
  ACSLStatementAnnotator stmtAnnotator;
  for (auto *func : functions) {
    std::string annotatedSrc = stmtAnnotator.annotateFunction(func,
                                                               options.acslStatements);
    // Insert into output stream
  }
}
```

#### CLI Option Parsing
```cpp
// In CommandLineOptions.cpp
cl::opt<std::string> ACSLStatements(
  "acsl-statements",
  cl::desc("Generate ACSL statement annotations (none|basic|full)"),
  cl::value_desc("level"),
  cl::init("none")
);
```

## Test Plan

### Test Suite Structure
`tests/ACSLStatementAnnotatorTest.cpp` with 15+ tests:

#### Core Functionality (6 tests)
1. **PointerDereferenceAssertion**: Verify assert generated before dereference
2. **ArrayAccessAssertion**: Verify bounds check for array access
3. **DivisionByZeroAssertion**: Verify divisor non-zero check
4. **BufferOverflowAssertion**: Verify buffer size check
5. **NullPointerAssertion**: Verify null check for nullable pointers
6. **CastAssertion**: Verify cast safety check

#### Assume Annotations (3 tests)
7. **ValidatedInputAssumption**: Verify assume after validation
8. **ConstructorAssumption**: Verify assume in constructor
9. **PlatformAssumption**: Verify platform-specific assumes

#### Check Annotations (3 tests)
10. **ProofMilestoneCheck**: Verify check at algorithm milestone
11. **InvariantMaintenanceCheck**: Verify invariant checks
12. **CustomProofObligationCheck**: Verify user-defined checks

#### Verbosity Levels (3 tests)
13. **NoneLevel**: Verify no annotations at none level
14. **BasicLevel**: Verify essential annotations at basic level
15. **FullLevel**: Verify comprehensive annotations at full level

### Test Methodology
- **TDD**: Write failing tests first
- **Isolation**: Each test covers one annotation pattern
- **Validation**: Parse output with Frama-C to ensure correctness
- **Coverage**: Aim for ≥95% code coverage

### Example Test Case
```cpp
TEST(ACSLStatementAnnotatorTest, PointerDereferenceAssertion) {
  const char *source = R"(
    int getValue(int *p) {
      return *p;
    }
  )";

  ACSLStatementAnnotator annotator;
  std::string result = annotator.annotateFunction(
    parseFunction(source, "getValue"),
    AnnotationLevel::Basic
  );

  EXPECT_THAT(result, HasSubstr("//@ assert \\valid(p);"));
  EXPECT_TRUE(framaCParses(result));
}
```

## Implementation Strategy

### Step 1: Foundation (TDD)
1. Create `include/ACSLStatementAnnotator.h` with interface
2. Create `tests/ACSLStatementAnnotatorTest.cpp` with first failing test
3. Implement minimal `src/ACSLStatementAnnotator.cpp` to pass test
4. Refactor and add next test
5. Repeat for all 15+ tests

### Step 2: Core Annotation Logic
1. Implement `visitStmt()` using RecursiveASTVisitor pattern
2. Implement `generateAssert()` for safety properties
3. Implement `generateAssume()` for validated contexts
4. Implement `generateCheck()` for proof obligations
5. Implement `needsAnnotation()` based on verbosity level

### Step 3: AST Analysis
1. Implement pointer dereference detection
2. Implement array access detection
3. Implement division operation detection
4. Implement cast operation detection
5. Implement buffer operation detection

### Step 4: Safety Property Extraction
1. Extract pointer validity from dereference
2. Extract bounds from array access
3. Extract non-zero from division
4. Extract buffer constraints from string ops
5. Extract type constraints from casts

### Step 5: Integration
1. Add CLI flag parsing
2. Integrate into transpiler pipeline
3. Add output formatting
4. Test end-to-end with sample programs

### Step 6: Validation
1. Run all 15+ unit tests (must pass 100%)
2. Run existing 37 tests from v1.17.0 (regression check)
3. Validate with Frama-C WP on sample programs
4. Performance benchmark vs. v1.17.0
5. Lint and type-check all code

## Verification Criteria

### Functional Correctness
- [ ] All 15+ unit tests passing
- [ ] All 37 regression tests passing (v1.17.0)
- [ ] Generated assertions provable by Frama-C WP
- [ ] No false positives (assertions failing incorrectly)

### Code Quality
- [ ] Zero linting errors (clang-tidy, cppcheck)
- [ ] Strong typing enforced (no implicit casts)
- [ ] SOLID principles followed
- [ ] Code coverage ≥95%

### Performance
- [ ] Transpilation time increase ≤5% at basic level
- [ ] Transpilation time increase ≤10% at full level
- [ ] Memory usage increase ≤10%

### Integration
- [ ] Frama-C parses 100% of generated annotations
- [ ] CLI flag works as documented
- [ ] Default behavior (none) preserves v1.17.0

## Dependencies

### External Dependencies
- Clang/LLVM 15+ (already present)
- Frama-C 27.0+ (for validation)
- Google Test (already present)

### Internal Dependencies
- No dependencies on other phases
- Enhances existing function annotation infrastructure

## Risks and Mitigation

### Risk 1: Annotation Spam (High Impact, Medium Probability)
**Mitigation**:
- Implement verbosity levels (none/basic/full)
- Use heuristics to avoid redundant assertions (e.g., if function contract already ensures \valid(p), don't add assert)
- Make `basic` level the recommended default

### Risk 2: False Positives (High Impact, Low Probability)
**Mitigation**:
- Extensive test suite with corner cases
- Validate with Frama-C WP on each test
- Conservative assertion generation (only when confident)

### Risk 3: Performance Impact (Medium Impact, Medium Probability)
**Mitigation**:
- Profile hot paths during implementation
- Optimize AST traversal (single-pass when possible)
- Target ≤5% impact at basic level

### Risk 4: Frama-C Incompatibility (High Impact, Low Probability)
**Mitigation**:
- Test against Frama-C after each test case
- Reference ACSL 1.17 specification strictly
- Run Frama-C CI tests before release

## Success Metrics

### Quantitative
- **Tests**: 15+ tests, 100% passing
- **Coverage**: ≥95% code coverage
- **Performance**: ≤10% transpilation time increase
- **Frama-C compatibility**: 100% parsing success

### Qualitative
- Annotations aid in understanding code safety properties
- Proof burden reduced (Frama-C proves more automatically)
- No degradation in output C code quality

## Next Steps

1. **Execute this plan**: Begin TDD implementation
2. **Parallel tasks**: Can run tests in parallel during development
3. **Review before release**: Separate agent reviews code
4. **Release v1.18.0**: Git-flow release after all criteria met

**Ready to execute**: Yes, all prerequisites met.
