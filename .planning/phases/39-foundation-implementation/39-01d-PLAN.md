# Phase 39-01d: Code Generation & Pipeline Completion

## Objective

Implement CodeGenerator (Stage 3) and integrate the complete 3-stage transpiler pipeline. Add documentation, perform code review, and finalize Phase 1 implementation.

**Goal:** Complete, working transpiler for basic C++ programs.

**Dependencies:** Phase 39-01c must be complete (all tests passing)

## Context

@docs/architecture/04-code-generator.md - CodeGenerator specification
@docs/architecture/01-pipeline-architecture.md - 3-stage pipeline
@docs/architecture/10-phase1-detailed-plan.md - Pipeline integration steps
@include/handlers/*.h - All implemented handlers

## Tasks

### Task 1: Implement CodeGenerator (Stage 3)
**Type**: auto
**Estimated**: 3-4 hours

**Action**: Implement C AST visitor that emits C source code

**Implementation:**

Create `include/CodeGenerator.h`:
```cpp
class CodeGenerator {
private:
    llvm::raw_ostream& headerStream_;
    llvm::raw_ostream& implStream_;
    clang::ASTContext& cContext_;
    int indentLevel_;

public:
    CodeGenerator(llvm::raw_ostream& header,
                  llvm::raw_ostream& impl,
                  clang::ASTContext& ctx);

    void generate(clang::TranslationUnitDecl* TU);

private:
    // Visitor methods
    void visitTranslationUnit(clang::TranslationUnitDecl* TU);
    void visitFunctionDecl(clang::FunctionDecl* FD);
    void visitVarDecl(clang::VarDecl* VD);
    void visitCompoundStmt(clang::CompoundStmt* CS);
    void visitReturnStmt(clang::ReturnStmt* RS);
    void visitBinaryOperator(clang::BinaryOperator* BO);
    void visitUnaryOperator(clang::UnaryOperator* UO);
    void visitDeclRefExpr(clang::DeclRefExpr* DRE);
    void visitIntegerLiteral(clang::IntegerLiteral* IL);
    void visitFloatingLiteral(clang::FloatingLiteral* FL);

    // Helpers
    void emitType(clang::QualType T);
    void emitIndent();
    bool shouldGoToHeader(clang::Decl* D);
};
```

Create `src/CodeGenerator.cpp` with implementation following specification

**Key Principles:**
- Pure emission - no translation decisions
- Just print what's in the C AST
- Proper indentation and formatting
- Header vs implementation separation

**Verification:**
- [ ] CodeGenerator compiles
- [ ] Emits valid C syntax
- [ ] Proper indentation
- [ ] Header/impl separation works
- [ ] All AST node types covered

---

### Task 2: Integrate Full Pipeline
**Type**: auto
**Estimated**: 2-3 hours

**Action**: Connect all 3 stages into complete transpiler

**Implementation:**

Create or update `src/Transpiler.cpp`:
```cpp
class Transpiler {
public:
    TranspilationResult transpile(const std::string& cppFile) {
        // Stage 1: Clang parses C++ → C++ AST
        clang::ASTContext* cppContext = parseC

ppFile(cppFile);

        // Stage 2: Handlers translate C++ AST → C AST
        clang::ASTContext* cContext = createCContext();
        CNodeBuilder builder(*cContext);
        HandlerContext context(*cppContext, *cContext, builder);

        // Register all handlers
        HandlerRegistry registry;
        registry.registerHandler(std::make_unique<FunctionHandler>());
        registry.registerHandler(std::make_unique<VariableHandler>());
        registry.registerHandler(std::make_unique<ExpressionHandler>());
        registry.registerHandler(std::make_unique<StatementHandler>());

        // Orchestrate translation
        TranslationOrchestrator orchestrator(registry, context);
        clang::TranslationUnitDecl* cTU = orchestrator.translate(cppContext->getTranslationUnitDecl());

        // Stage 3: CodeGenerator emits C source
        std::string headerFile = cppFile + ".h";
        std::string implFile = cppFile + ".c";

        std::error_code EC;
        llvm::raw_fd_ostream headerOS(headerFile, EC);
        llvm::raw_fd_ostream implOS(implFile, EC);

        CodeGenerator generator(headerOS, implOS, *cContext);
        generator.generate(cTU);

        return {true, headerFile, implFile};
    }
};
```

**Verification:**
- [ ] Full pipeline works end-to-end
- [ ] Can transpile simple C++ programs
- [ ] Generated C compiles
- [ ] Generated C runs correctly

---

### Task 3: Run All Tests
**Type**: auto
**Estimated**: 1 hour

**Action**: Execute complete test suite and verify 100% pass rate

**Test Execution:**
```bash
cd build
ctest --output-on-failure
```

**Expected Results:**
- FunctionHandler tests: 3+ passing
- VariableHandler tests: 15+ passing
- ExpressionHandler tests: 35+ passing
- StatementHandler tests: 12+ passing
- Integration tests: 25+ passing
- E2E tests: 10+ passing
- **Total: 100+ tests passing (100%)**

**Verification:**
- [ ] All unit tests pass
- [ ] All integration tests pass
- [ ] All E2E tests pass
- [ ] No test failures
- [ ] No memory leaks (valgrind)

---

### Task 4: Documentation
**Type**: auto
**Estimated**: 1-2 hours

**Action**: Document all implemented code

**Documentation Tasks:**
1. Add Doxygen comments to all public APIs
2. Document handler interfaces
3. Create usage examples
4. Update README if needed
5. Document CodeGenerator interface
6. Add inline comments for complex logic

**Verification:**
- [ ] All public APIs documented
- [ ] Usage examples provided
- [ ] Code is self-documenting
- [ ] No undocumented public methods

---

### Task 5: Code Review & Refactoring
**Type**: auto
**Estimated**: 2-3 hours

**Action**: Review all code for quality and refactor as needed

**Review Checklist:**
1. Run static analysis (clang-tidy, cppcheck)
2. Check for code duplication (DRY violations)
3. Verify SOLID principles compliance
4. Identify complex methods that need simplification
5. Check for proper error handling
6. Verify memory management (no leaks)
7. Check for performance issues
8. Ensure consistent coding style

**Refactoring:**
- Extract duplicated code into helper methods
- Simplify complex methods (keep under 20 lines)
- Improve naming where unclear
- Add const correctness
- Optimize hot paths if needed

**Verification:**
- [ ] No static analysis warnings
- [ ] Code follows SOLID principles
- [ ] No duplicated logic
- [ ] All methods are focused and simple
- [ ] 100% test coverage maintained

---

### Task 6: Final Verification
**Type**: auto
**Estimated**: 1 hour

**Action**: Final comprehensive verification

**Verification Checklist:**

1. **Functionality:**
   - [ ] Can transpile basic C++ to C
   - [ ] Generated C compiles
   - [ ] Generated C executes correctly
   - [ ] All Phase 1 features working

2. **Tests:**
   - [ ] 100+ tests passing
   - [ ] 100% handler coverage
   - [ ] Integration validated
   - [ ] E2E validated

3. **Code Quality:**
   - [ ] No compiler warnings
   - [ ] No static analysis issues
   - [ ] SOLID principles followed
   - [ ] Well documented
   - [ ] Clean and readable

4. **Architecture:**
   - [ ] 3-stage pipeline implemented
   - [ ] Handler chain working
   - [ ] Follows design docs exactly
   - [ ] Ready for Phase 2

---

## Verification

**Phase 39-01d (and Full Phase 1) Completion Criteria:**

1. **CodeGenerator:**
   - [ ] Implemented and working
   - [ ] Emits valid C code
   - [ ] Follows spec exactly

2. **Pipeline:**
   - [ ] All 3 stages integrated
   - [ ] End-to-end working
   - [ ] Can transpile programs

3. **Tests:**
   - [ ] 100+ tests passing (100%)
   - [ ] All verification gates passed

4. **Quality:**
   - [ ] No warnings/errors
   - [ ] Well documented
   - [ ] Code review complete
   - [ ] Ready for production use

## Success Criteria

✅ Complete transpiler working end-to-end
✅ CodeGenerator implemented (Stage 3)
✅ Full pipeline integrated
✅ 100+ tests passing
✅ Code quality excellent
✅ Documentation complete
✅ Ready for Phase 2 (Control Flow)

**Estimated Total:** 10-13 hours

## Output

Create `.planning/phases/39-foundation-implementation/39-01d-SUMMARY.md` with:

**Deliverables:**
- CodeGenerator implementation
- Full pipeline integration
- Complete test suite passing
- Documentation complete

**Final Statistics:**
- Total files created in Phase 1
- Total LOC (implementation + tests)
- Total tests: 100+
- Test pass rate: 100%
- Code coverage: 100% for handlers

**Phase 1 Achievement:**
- Foundation complete
- All basic features working
- Pipeline validated
- Ready for Phase 2

**Next Steps:**
- Phase 2: Control Flow (if/while/for/switch)
- Phase 3: Global Variables

**Final Commit:**
Format: `feat(phase1): Complete Phase 1 - Basic Functions & Arithmetic`
