# Exception Handler Dispatcher Integration - Planning Phase

## Objective

Create a comprehensive, actionable implementation plan for migrating exception handling components (TryCatchTransformer, ThrowTranslator, ExceptionFrameGenerator) to the dispatcher pattern, addressing all technical debt, and establishing complete test coverage.

**Why this matters**: This plan will guide the implementation phase, ensuring systematic integration of exception handling into the transpiler pipeline with minimal risk and full test coverage.

## Context

### Research Findings
**@.prompts/060-exception-dispatcher-research/exception-dispatcher-research.md** - Technical analysis including:
- Dispatcher integration patterns from existing handlers
- Current architecture of all 3 exception components
- Technical debt catalog (manual mangling, placeholder methods)
- Integration points with other handlers
- Test migration strategy
- Complexity assessment

### Existing Documentation
**@EXCEPTION_HANDLING_STATUS.md** - Status overview documenting:
- Complete standalone implementation
- Missing dispatcher integration
- Technical debt items
- Migration path recommendations

### Dispatcher Pattern Reference
Existing dispatcher handlers in `include/dispatch/` and `src/dispatch/` demonstrate:
- Registration pattern (`registerWith(CppToCVisitorDispatcher&)`)
- Handler method signatures
- NameMangler API integration
- Inter-handler communication

## Requirements

### 1. Implementation Phases

**Design the migration as phases** that can be implemented and tested incrementally:

```xml
<implementation_phases>
  <phase number="1" name="Handler Skeleton Creation">
    <scope>
      <!-- What handlers to create, what AST nodes they handle -->
      <handlers>
        <handler name="TryStmtHandler">
          <ast_node>CXXTryStmt</ast_node>
          <delegation>Delegates to TryCatchTransformer</delegation>
          <files>include/dispatch/TryStmtHandler.h, src/dispatch/TryStmtHandler.cpp</files>
        </handler>
        <!-- Repeat for ThrowExprHandler, etc. -->
      </handlers>
    </scope>

    <deliverables>
      <!-- Concrete files to create -->
      <file path="include/dispatch/TryStmtHandler.h">Header with registration method</file>
      <file path="src/dispatch/TryStmtHandler.cpp">Implementation delegating to transformer</file>
    </deliverables>

    <tests>
      <!-- How to verify this phase -->
      <test type="unit">Handler registration with dispatcher</test>
      <test type="unit">Predicate correctly identifies AST nodes</test>
    </tests>

    <success_criteria>
      <!-- How to know phase is complete -->
      <criterion>Handlers compile without errors</criterion>
      <criterion>Handlers register with dispatcher successfully</criterion>
      <criterion>Predicates tested with AST node samples</criterion>
    </success_criteria>

    <risks>
      <!-- What could go wrong -->
      <risk probability="low" impact="medium">Signature mismatch with dispatcher interface</risk>
    </risks>
  </phase>

  <phase number="2" name="Name Mangling Migration">
    <scope>
      <!-- Replace all manual mangling with NameMangler API -->
      <components>
        <component>TryCatchTransformer</component>
        <component>ThrowTranslator</component>
        <component>ExceptionFrameGenerator</component>
      </components>

      <replacements>
        <!-- Specific code changes needed -->
        <replacement>
          <location>TryCatchTransformer::getMangledTypeName()</location>
          <from>Manual string concatenation</from>
          <to>cpptoc::mangle_class(record)</to>
        </replacement>
        <!-- More replacements from research phase -->
      </replacements>
    </scope>

    <deliverables>
      <!-- What changes -->
      <modification>Update TryCatchTransformer to use NameMangler</modification>
      <modification>Update ThrowTranslator to use NameMangler</modification>
      <modification>Update ExceptionFrameGenerator to use NameMangler</modification>
    </deliverables>

    <tests>
      <!-- Existing tests should pass with new implementation -->
      <test type="unit">All existing component unit tests pass</test>
      <test type="integration">Name mangling consistency verified</test>
    </tests>

    <success_criteria>
      <criterion>No manual string mangling remains</criterion>
      <criterion>All component tests pass</criterion>
      <criterion>Names match dispatcher pattern</criterion>
    </success_criteria>

    <risks>
      <risk probability="medium" impact="high">NameMangler API doesn't support exception-specific patterns</risk>
    </risks>
  </phase>

  <phase number="3" name="Placeholder Method Resolution">
    <scope>
      <!-- Replace placeholder methods with dispatcher delegation -->
      <methods>
        <method component="TryCatchTransformer">
          <name>stmtToString()</name>
          <current>Placeholder or hardcoded</current>
          <solution>Delegate to dispatcher.handleStmt()</solution>
        </method>
        <method component="ThrowTranslator">
          <name>exprToString()</name>
          <current>Placeholder or hardcoded</current>
          <solution>Delegate to dispatcher.handleExpr()</solution>
        </method>
      </methods>
    </scope>

    <deliverables>
      <modification>Update component methods to accept dispatcher reference</modification>
      <modification>Replace placeholders with dispatcher calls</modification>
    </deliverables>

    <tests>
      <test type="integration">Recursive translation of nested expressions works</test>
      <test type="integration">Statement translation within try blocks works</test>
    </tests>

    <success_criteria>
      <criterion>No placeholder methods remain</criterion>
      <criterion>Recursive translation tested</criterion>
    </success_criteria>

    <risks>
      <risk probability="high" impact="high">Circular dependencies between handlers and components</risk>
    </risks>
  </phase>

  <phase number="4" name="Dispatcher Integration">
    <scope>
      <!-- Wire handlers into dispatcher -->
      <registration>
        <location>Main dispatcher initialization</location>
        <handlers>TryStmtHandler, ThrowExprHandler</handlers>
      </registration>

      <integration_points>
        <!-- How exception handlers interact with other handlers -->
        <interaction>
          <scenario>Method call inside try block</scenario>
          <handlers>TryStmtHandler, MethodHandler</handlers>
          <solution>TryStmtHandler delegates body translation to dispatcher</solution>
        </interaction>
      </integration_points>
    </scope>

    <deliverables>
      <modification>Register exception handlers in CppToCVisitorDispatcher</modification>
      <modification>Update StatementHandler to include exception statements</modification>
    </deliverables>

    <tests>
      <test type="integration">End-to-end try-catch translation</test>
      <test type="integration">Exception handling with virtual methods</test>
      <test type="integration">Exception handling with constructors</test>
    </tests>

    <success_criteria>
      <criterion>All handlers registered and functional</criterion>
      <criterion>Integration tests pass</criterion>
    </success_criteria>

    <risks>
      <risk probability="medium" impact="high">Handler registration order affects correctness</risk>
    </risks>
  </phase>

  <phase number="5" name="Test Migration">
    <scope>
      <!-- Migrate existing tests to dispatcher pattern -->
      <test_migration_strategy>
        <existing_tests>
          <test file="tests/TryCatchTransformerTest.cpp">
            <migration_type>Update to use dispatcher</migration_type>
            <new_location>tests/unit/handlers/TryStmtHandlerTest.cpp</new_location>
          </test>
          <!-- List all 9 test files -->
        </existing_tests>

        <new_tests>
          <test file="tests/integration/handlers/ExceptionHandlingIntegrationTest.cpp">
            <coverage>Cross-handler exception scenarios</coverage>
          </test>
        </new_tests>
      </test_migration_strategy>
    </scope>

    <deliverables>
      <creation>New dispatcher-based unit tests</creation>
      <migration>Updated existing tests</migration>
      <creation>New integration tests for cross-handler scenarios</creation>
    </deliverables>

    <tests>
      <!-- Meta: tests for the test migration -->
      <test type="verification">All migrated tests pass</test>
      <test type="verification">Test coverage maintained or improved</test>
    </tests>

    <success_criteria>
      <criterion>All existing test coverage preserved</criterion>
      <criterion>New dispatcher-specific tests added</criterion>
      <criterion>Integration tests cover cross-handler scenarios</criterion>
    </success_criteria>

    <risks>
      <risk probability="low" impact="medium">Test migration breaks existing coverage</risk>
    </risks>
  </phase>

  <!-- Add more phases as needed based on research findings -->
</implementation_phases>
```

### 2. Detailed Task Breakdown

**For each phase, break down into specific tasks:**

```xml
<task_breakdown>
  <phase_ref>1</phase_ref>

  <task number="1.1" estimated_effort="2 hours">
    <description>Create TryStmtHandler skeleton</description>
    <steps>
      <step>Create include/dispatch/TryStmtHandler.h with class declaration</step>
      <step>Add registerWith() static method signature</step>
      <step>Add canHandle() predicate signature</step>
      <step>Add handleTryStmt() visitor signature</step>
      <step>Create src/dispatch/TryStmtHandler.cpp with stubs</step>
    </steps>
    <dependencies>None</dependencies>
    <verification>Compiles without errors, headers included correctly</verification>
  </task>

  <task number="1.2" estimated_effort="1 hour">
    <description>Implement canHandle() predicate for TryStmtHandler</description>
    <steps>
      <step>Check if Decl is CXXTryStmt</step>
      <step>Add assertions for null checks</step>
      <step>Write unit test for predicate</step>
    </steps>
    <dependencies>Task 1.1</dependencies>
    <verification>Unit test passes with various AST node types</verification>
  </task>

  <!-- Continue for all tasks in all phases -->
</task_breakdown>
```

### 3. Technical Debt Resolution Plan

**Map each technical debt item to specific tasks:**

```xml
<technical_debt_resolution>
  <debt_item id="TD1">
    <description>Manual name mangling in TryCatchTransformer</description>
    <locations>
      <location file="src/TryCatchTransformer.cpp" line="42">getMangledTypeName()</location>
      <location file="src/TryCatchTransformer.cpp" line="78">getConstructorName()</location>
    </locations>
    <resolution>
      <phase_ref>2</phase_ref>
      <task_ref>2.1</task_ref>
      <replacement>Use cpptoc::mangle_class() and cpptoc::mangle_constructor()</replacement>
    </resolution>
    <verification>
      <test>Existing unit tests pass with new API</test>
      <test>Names match dispatcher pattern</test>
    </verification>
  </debt_item>

  <debt_item id="TD2">
    <description>Placeholder stmtToString() method</description>
    <locations>
      <location file="src/TryCatchTransformer.cpp" line="156">stmtToString()</location>
    </locations>
    <resolution>
      <phase_ref>3</phase_ref>
      <task_ref>3.1</task_ref>
      <replacement>Accept dispatcher reference, call dispatcher.handleStmt()</replacement>
    </resolution>
    <verification>
      <test>Integration test with nested statements in try block</test>
    </verification>
  </debt_item>

  <!-- Map all technical debt items from research phase -->
</technical_debt_resolution>
```

### 4. Test Strategy

**Comprehensive testing plan for each phase:**

```xml
<test_strategy>
  <unit_tests>
    <test_group phase="1">
      <test name="TryStmtHandler_Registration">
        <description>Verify handler registers with dispatcher</description>
        <setup>Create dispatcher, call TryStmtHandler::registerWith()</setup>
        <assertion>Handler added to dispatcher's handler list</assertion>
      </test>

      <test name="TryStmtHandler_Predicate">
        <description>Verify canHandle() correctly identifies CXXTryStmt</description>
        <setup>Create various AST node types</setup>
        <assertion>Returns true only for CXXTryStmt</assertion>
      </test>
    </test_group>

    <test_group phase="2">
      <test name="NameMangling_TryCatch">
        <description>Verify NameMangler integration in TryCatchTransformer</description>
        <setup>Create exception class with TryCatchTransformer</setup>
        <assertion>Mangled names match cpptoc::mangle_class() output</assertion>
      </test>
    </test_group>

    <!-- Continue for all phases -->
  </unit_tests>

  <integration_tests>
    <test name="TryCatch_EndToEnd">
      <description>Complete try-catch translation through dispatcher</description>
      <input>C++ try-catch block with exception class</input>
      <expected_output>C setjmp/longjmp code with mangled names</expected_output>
      <phases_tested>1, 2, 3, 4</phases_tested>
    </test>

    <test name="Exception_VirtualMethod">
      <description>Exception handling with virtual method calls</description>
      <input>try block calling virtual method that throws</input>
      <expected_output>Correct vtable dispatch with exception handling</expected_output>
      <handlers_involved>TryStmtHandler, MethodHandler, ThrowExprHandler</handlers_involved>
    </test>

    <!-- More integration scenarios -->
  </integration_tests>

  <migration_tests>
    <existing_test file="tests/TryCatchTransformerTest.cpp">
      <migration_strategy>
        <step>Create tests/unit/handlers/TryStmtHandlerTest.cpp</step>
        <step>Convert standalone transformer tests to dispatcher pattern</step>
        <step>Add DispatcherTestHelper fixture</step>
        <step>Verify all test cases pass with dispatcher</step>
      </migration_strategy>
    </existing_test>

    <!-- Map all 9 existing test files -->
  </migration_tests>
</test_strategy>
```

### 5. Risk Mitigation

**Identify risks from research and plan mitigations:**

```xml
<risk_mitigation>
  <risk id="R1" probability="high" impact="high">
    <description>Circular dependencies between handlers and transformers</description>
    <detection_phase>Phase 3 - Placeholder method resolution</detection_phase>
    <mitigation>
      <approach>Dependency Injection</approach>
      <detail>Pass dispatcher reference to transformer methods at call time, not construction</detail>
      <fallback>Keep transformers stateless, accept all dependencies as parameters</fallback>
    </mitigation>
    <contingency>If DI fails, create intermediate interface to break cycle</contingency>
  </risk>

  <risk id="R2" probability="medium" impact="high">
    <description>NameMangler API doesn't support exception-specific patterns</description>
    <detection_phase>Phase 2 - Name mangling migration</detection_phase>
    <mitigation>
      <approach>Extend NameMangler API</approach>
      <detail>Add cpptoc::mangle_exception_frame() and related functions</detail>
      <fallback>Create ExceptionNameMangler adapter wrapping NameMangler</fallback>
    </mitigation>
    <contingency>Document exception-specific mangling as technical debt for Phase 2.1</contingency>
  </risk>

  <!-- Map all risks from research phase -->
</risk_mitigation>
```

### 6. Integration Points

**Plan how exception handlers coordinate with existing handlers:**

```xml
<integration_points>
  <scenario name="Method Call in Try Block">
    <description>Try block containing method calls</description>
    <handlers_involved>
      <handler>TryStmtHandler</handler>
      <handler>MethodHandler</handler>
    </handlers_involved>
    <coordination>
      <step>TryStmtHandler handles CXXTryStmt</step>
      <step>TryStmtHandler delegates try body to dispatcher</step>
      <step>Dispatcher routes method calls to MethodHandler</step>
      <step>TryStmtHandler wraps result in setjmp guard</step>
    </coordination>
    <phase_implementation>Phase 4</phase_implementation>
    <test>Integration test with virtual method call in try block</test>
  </scenario>

  <scenario name="Throw in Constructor">
    <description>Constructor body containing throw expression</description>
    <handlers_involved>
      <handler>ConstructorHandler</handler>
      <handler>ThrowExprHandler</handler>
    </handlers_involved>
    <coordination>
      <step>ConstructorHandler handles CXXConstructorDecl</step>
      <step>ConstructorHandler delegates body to dispatcher</step>
      <step>ThrowExprHandler handles CXXThrowExpr in body</step>
      <step>ThrowExprHandler generates longjmp with exception object</step>
    </coordination>
    <phase_implementation>Phase 4</phase_implementation>
    <test>Integration test with constructor throwing exception</test>
  </scenario>

  <!-- Map all integration scenarios from research -->
</integration_points>
```

### 7. Success Criteria

**Define what "done" means for the entire migration:**

```xml
<success_criteria>
  <criterion category="functionality">
    <description>All exception handling features work through dispatcher</description>
    <verification>E2E tests for try-catch-throw pass</verification>
  </criterion>

  <criterion category="technical_debt">
    <description>No manual name mangling remains</description>
    <verification>Grep for manual string concatenation patterns returns empty</verification>
  </criterion>

  <criterion category="technical_debt">
    <description>No placeholder methods remain</description>
    <verification>All stmtToString/exprToString replaced with dispatcher calls</verification>
  </criterion>

  <criterion category="testing">
    <description>All existing test coverage preserved</description>
    <verification>9 existing test files migrated and passing</verification>
  </criterion>

  <criterion category="testing">
    <description>Dispatcher-specific tests added</description>
    <verification>Unit tests for each handler, integration tests for cross-handler scenarios</verification>
  </criterion>

  <criterion category="architecture">
    <description>Handlers follow dispatcher pattern</description>
    <verification>Registration method, predicate, visitor match existing handlers</verification>
  </criterion>

  <criterion category="architecture">
    <description>Components remain reusable</description>
    <verification>TryCatchTransformer, ThrowTranslator, ExceptionFrameGenerator can be tested standalone</verification>
  </criterion>

  <criterion category="documentation">
    <description>All new handlers documented</description>
    <verification>Header comments explain responsibility, delegation, integration</verification>
  </criterion>
</success_criteria>
```

## Output Specification

**Write to**: `.prompts/061-exception-dispatcher-plan/exception-dispatcher-plan.md`

### Required Structure

```xml
<?xml version="1.0" encoding="UTF-8"?>
<plan>
  <metadata>
    <version>v1</version>
    <date>YYYY-MM-DD</date>
    <confidence>High/Medium/Low - How confident in plan feasibility</confidence>
    <dependencies>
      <!-- What must exist before implementation can start -->
      <dependency>Research findings confirmed</dependency>
      <dependency>User approval on approach</dependency>
    </dependencies>
    <open_questions>
      <!-- What remains uncertain -->
      <question>Questions requiring user decision before starting</question>
    </open_questions>
    <assumptions>
      <!-- What was assumed during planning -->
      <assumption>Key assumptions affecting plan</assumption>
    </assumptions>
  </metadata>

  <!-- Include all planning sections from Requirements -->
  <implementation_phases>...</implementation_phases>
  <task_breakdown>...</task_breakdown>
  <technical_debt_resolution>...</technical_debt_resolution>
  <test_strategy>...</test_strategy>
  <risk_mitigation>...</risk_mitigation>
  <integration_points>...</integration_points>
  <success_criteria>...</success_criteria>

  <execution_order>
    <!-- Recommended order for implementing phases -->
    <phase_sequence>
      <phase_ref priority="1">Phase 1 - Handler Skeleton Creation</phase_ref>
      <rationale>Must create handlers before integrating</rationale>
    </phase_sequence>
    <!-- Continue for all phases -->
  </execution_order>

  <estimated_effort>
    <total_hours>Total estimated implementation time</total_hours>
    <breakdown>
      <phase_ref>1</phase_ref>
      <hours>X hours</hours>
    </breakdown>
    <!-- For all phases -->
  </estimated_effort>

  <recommendations>
    <!-- Key recommendations for implementation phase -->
    <recommendation priority="critical">
      <description>Critical recommendation affecting success</description>
      <rationale>Why this is critical</rationale>
    </recommendation>
  </recommendations>
</plan>
```

### Quality Requirements

**Verification Checklist** (complete before finalizing):
- [ ] All research findings incorporated into plan
- [ ] All technical debt items mapped to specific tasks
- [ ] All phases have clear deliverables and success criteria
- [ ] All risks identified with mitigation strategies
- [ ] All integration points planned with coordination steps
- [ ] Test strategy covers unit, integration, and migration
- [ ] Task breakdown is actionable and specific
- [ ] Effort estimates provided for each task
- [ ] Dependencies between tasks identified
- [ ] Execution order recommended

**Quality Report** (include in output):
```xml
<quality_report>
  <research_coverage>
    <!-- How well research findings are incorporated -->
    <finding>Research finding X</finding>
    <plan_reference>Addressed in Phase Y, Task Z</plan_reference>
  </research_coverage>

  <completeness>
    <!-- Assessment of plan completeness -->
    <aspect>Technical debt resolution</aspect>
    <status>All items mapped</status>
  </completeness>

  <feasibility>
    <!-- Assessment of plan feasibility -->
    <aspect>Estimated effort</aspect>
    <assessment>Conservative estimates based on similar migrations</assessment>
  </feasibility>

  <confidence_rationale>
    <!-- Why the overall confidence level was chosen -->
    Explanation of confidence level
  </confidence_rationale>
</quality_report>
```

## Success Criteria

- [ ] All phases defined with clear scope and deliverables
- [ ] All tasks broken down with effort estimates
- [ ] All technical debt items mapped to resolution tasks
- [ ] Complete test strategy (unit, integration, migration)
- [ ] All risks identified with mitigation plans
- [ ] Integration points planned with handler coordination
- [ ] Success criteria defined for entire migration
- [ ] Execution order recommended
- [ ] Total effort estimated
- [ ] Output saved to exception-dispatcher-plan.md with proper XML structure
- [ ] SUMMARY.md created with one-liner, key decisions, and blockers
- [ ] Confidence, dependencies, open questions, and assumptions documented

## SUMMARY.md Requirement

**Create**: `.prompts/061-exception-dispatcher-plan/SUMMARY.md`

Required sections:
- **One-liner**: Substantive summary of the plan (not generic "plan created")
- **Version**: v1
- **Key Decisions**: Top 3-5 critical decisions made in the plan
- **Decisions Needed**: Questions requiring user approval before implementation
- **Blockers**: External impediments preventing implementation start
- **Next Step**: "Create implementation prompt (062-exception-dispatcher-implement)" or "Begin implementation"

---

**Execution notes**: Use extended thinking for complex planning. Reference research findings extensively. Create actionable, specific tasks. Be conservative with effort estimates. Identify all risks and mitigations. Distinguish verified from assumed plan elements in quality report.
