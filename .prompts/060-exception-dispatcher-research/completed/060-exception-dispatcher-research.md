# Exception Handler Dispatcher Integration - Research Phase

## Objective

Conduct deep technical analysis of exception handling components (TryCatchTransformer, ThrowTranslator, ExceptionFrameGenerator) to understand their current architecture, identify integration points with the dispatcher pattern, and document all technical debt for resolution during migration.

**Why this matters**: Exception handling is fully implemented but isolated from the new dispatcher architecture. This research will map the integration path and identify all changes needed to bring exception handling into the dispatcher-based transpiler pipeline.

## Context

### Existing Documentation
**@EXCEPTION_HANDLING_STATUS.md** - Current status analysis showing:
- ✅ Complete implementation (TryCatchTransformer, ThrowTranslator, ExceptionFrameGenerator)
- ❌ NOT integrated with dispatcher pattern
- ⚠️ Uses manual name mangling instead of NameMangler API
- ⚠️ Has placeholder methods (stmtToString, exprToString)
- 9 existing test files for standalone components

### Dispatcher Pattern Examples
**!** Search for existing dispatcher handlers in `include/dispatch/` and `src/dispatch/` to understand:
- Registration pattern (`registerWith(CppToCVisitorDispatcher&)`)
- Handler method signatures (`static void handleDecl(...)`)
- Integration with NameMangler API
- Communication between handlers
- Test patterns for dispatcher-integrated handlers

### Exception Handling Components
**!** Analyze current implementation:
- `include/TryCatchTransformer.h` + `src/TryCatchTransformer.cpp`
- `include/ThrowTranslator.h` + `src/ThrowTranslator.cpp`
- `include/ExceptionFrameGenerator.h` + `src/ExceptionFrameGenerator.cpp`

## Requirements

### 1. Dispatcher Pattern Analysis

**Study existing dispatcher handlers** to extract integration patterns:

```xml
<dispatcher_patterns>
  <registration>
    <!-- How handlers register with dispatcher -->
    <example_handler>MethodHandler, StatementHandler, etc.</example_handler>
    <registration_method>static void registerWith(...)</registration_method>
    <ast_node_types>Which AST node types they register for</ast_node_types>
  </registration>

  <handler_methods>
    <!-- Handler method signatures and patterns -->
    <method_signature>Complete signature of handleDecl/handleStmt/handleExpr methods</method_signature>
    <dispatcher_access>How handlers access dispatcher for recursive calls</dispatcher_access>
    <state_management>How handlers store/access shared state</state_management>
  </handler_methods>

  <name_mangling_integration>
    <!-- How handlers use NameMangler API -->
    <api_usage>Which cpptoc::mangle_* functions are used</api_usage>
    <examples>Concrete examples from existing handlers</examples>
    <pattern>Common patterns for type/method/class name mangling</pattern>
  </name_mangling_integration>

  <inter_handler_communication>
    <!-- How handlers interact with each other -->
    <shared_data>What data is shared between handlers</shared_data>
    <delegation>How one handler calls another</delegation>
    <context_passing>How context flows through handler chain</context_passing>
  </inter_handler_communication>
</dispatcher_patterns>
```

### 2. Exception Component Analysis

**For each component** (TryCatchTransformer, ThrowTranslator, ExceptionFrameGenerator):

```xml
<component_analysis name="TryCatchTransformer">
  <current_architecture>
    <responsibilities>What does this class do?</responsibilities>
    <ast_nodes_handled>Which Clang AST nodes does it process?</ast_nodes_handled>
    <dependencies>What other classes/utilities does it depend on?</dependencies>
    <outputs>What C code does it generate?</outputs>
  </current_architecture>

  <technical_debt>
    <manual_mangling>
      <locations>File:line where manual name mangling occurs</locations>
      <pattern>What pattern is currently used (e.g., className + "_init")</pattern>
      <replacement>Which NameMangler API function should replace it</replacement>
    </manual_mangling>

    <placeholder_methods>
      <method>stmtToString(), exprToString(), etc.</method>
      <current_implementation>What do they currently do?</current_implementation>
      <dispatcher_solution>How should dispatcher handle this recursively?</dispatcher_solution>
    </placeholder_methods>

    <other_debt>Any additional issues discovered</other_debt>
  </technical_debt>

  <integration_requirements>
    <handler_creation>
      <handler_name>Proposed dispatcher handler name</handler_name>
      <ast_node_type>Clang AST node type to register for</ast_node_type>
      <delegation>How handler delegates to existing component</delegation>
    </handler_creation>

    <modifications_needed>
      <to_component>Changes needed to existing component class</to_component>
      <to_tests>Changes needed to existing tests</to_tests>
      <new_tests>New dispatcher-specific tests needed</new_tests>
    </modifications_needed>
  </integration_requirements>
</component_analysis>
```

**Repeat for ThrowTranslator and ExceptionFrameGenerator**.

### 3. Test Strategy Analysis

**Analyze existing tests** to plan migration:

```xml
<test_analysis>
  <existing_tests>
    <test_file>tests/TryCatchTransformerTest.cpp</test_file>
    <test_type>Unit test, integration test, E2E test</test_type>
    <coverage>What functionality is covered</coverage>
    <dispatcher_compatibility>Can it be adapted or needs rewrite?</dispatcher_compatibility>
  </existing_tests>

  <!-- Repeat for all 9 test files -->

  <dispatcher_test_patterns>
    <!-- Study existing dispatcher test patterns -->
    <example>Path to example dispatcher test</example>
    <pattern>How tests create dispatcher, register handlers, run transforms</pattern>
    <assertions>What assertions are used to verify output</assertions>
  </dispatcher_test_patterns>

  <migration_strategy>
    <tests_to_migrate>Which tests can be updated vs rewritten</tests_to_migrate>
    <new_tests_needed>What additional test coverage is needed</new_tests_needed>
    <test_fixtures>What test fixtures/helpers should be created</test_fixtures>
  </migration_strategy>
</test_analysis>
```

### 4. Integration Points Discovery

**Identify where exception handlers interact with other handlers:**

```xml
<integration_points>
  <method_calls_in_try>
    <!-- How TryStmtHandler works with MethodHandler/FunctionHandler -->
    <scenario>Method call inside try block</scenario>
    <handler_interaction>Which handlers are involved</handler_interaction>
    <current_gap>What doesn't work today</current_gap>
  </method_calls_in_try>

  <throw_in_constructor>
    <scenario>throw inside constructor body</scenario>
    <handler_interaction>ThrowExprHandler + ConstructorHandler</handler_interaction>
    <current_gap>What doesn't work today</current_gap>
  </throw_in_constructor>

  <exception_class_translation>
    <scenario>Exception class with members, methods, inheritance</scenario>
    <handler_interaction>How RecordHandler, MethodHandler interact with exception translation</handler_interaction>
    <current_gap>What doesn't work today</current_gap>
  </exception_class_translation>

  <!-- Add more integration scenarios as discovered -->
</integration_points>
```

### 5. Migration Complexity Assessment

**Estimate effort and identify risks:**

```xml
<complexity_assessment>
  <handler_creation>
    <effort>Low/Medium/High</effort>
    <rationale>Why this rating</rationale>
    <risks>What could go wrong</risks>
  </handler_creation>

  <technical_debt_resolution>
    <effort>Low/Medium/High</effort>
    <rationale>Why this rating</rationale>
    <risks>What could go wrong</risks>
  </technical_debt_resolution>

  <test_migration>
    <effort>Low/Medium/High</effort>
    <rationale>Why this rating</rationale>
    <risks>What could go wrong</risks>
  </test_migration>

  <overall>
    <estimated_effort>Total effort estimate</estimated_effort>
    <critical_path>What must be done first</critical_path>
    <dependencies>External dependencies or blockers</dependencies>
  </overall>
</complexity_assessment>
```

## Output Specification

**Write to**: `.prompts/060-exception-dispatcher-research/exception-dispatcher-research.md`

### Required Structure

```xml
<?xml version="1.0" encoding="UTF-8"?>
<research>
  <metadata>
    <version>v1</version>
    <date>YYYY-MM-DD</date>
    <confidence>High/Medium/Low - How confident in findings</confidence>
    <dependencies>
      <!-- What's needed before planning phase -->
      <dependency>List any missing information or decisions needed</dependency>
    </dependencies>
    <open_questions>
      <!-- What remains uncertain -->
      <question>Unanswered questions that affect planning</question>
    </open_questions>
    <assumptions>
      <!-- What was assumed during research -->
      <assumption>Key assumptions made</assumption>
    </assumptions>
  </metadata>

  <!-- Include all analysis sections from Requirements -->
  <dispatcher_patterns>...</dispatcher_patterns>
  <component_analysis name="TryCatchTransformer">...</component_analysis>
  <component_analysis name="ThrowTranslator">...</component_analysis>
  <component_analysis name="ExceptionFrameGenerator">...</component_analysis>
  <test_analysis>...</test_analysis>
  <integration_points>...</integration_points>
  <complexity_assessment>...</complexity_assessment>

  <recommendations>
    <!-- Key recommendations for planning phase -->
    <recommendation priority="high">Specific actionable recommendation</recommendation>
  </recommendations>
</research>
```

### Quality Requirements

**Verification Checklist** (complete before finalizing):
- [ ] Examined at least 3 existing dispatcher handlers for patterns
- [ ] Analyzed all 3 exception handling components thoroughly
- [ ] Identified all locations of manual name mangling
- [ ] Identified all placeholder methods requiring dispatcher delegation
- [ ] Reviewed all 9 existing test files
- [ ] Found examples of dispatcher test patterns
- [ ] Identified all integration points with other handlers
- [ ] Documented all assumptions made during research

**Quality Report** (include in output):
```xml
<quality_report>
  <sources_consulted>
    <!-- List all files examined with brief notes -->
    <source path="include/dispatch/MethodHandler.h">Registration pattern example</source>
  </sources_consulted>

  <verification_status>
    <!-- Which findings are verified vs assumed -->
    <verified>Findings confirmed by reading actual code</verified>
    <assumed>Findings based on inference/pattern matching</assumed>
  </verification_status>

  <confidence_rationale>
    <!-- Why the overall confidence level was chosen -->
    Explanation of confidence level
  </confidence_rationale>
</quality_report>
```

## Success Criteria

- [ ] All 3 exception components analyzed with technical debt cataloged
- [ ] Dispatcher integration pattern fully understood and documented
- [ ] All manual name mangling locations identified with replacement APIs specified
- [ ] All placeholder methods identified with dispatcher solutions proposed
- [ ] Test migration strategy defined
- [ ] Integration points with other handlers documented
- [ ] Complexity assessment completed with effort estimates
- [ ] Output saved to exception-dispatcher-research.md with proper XML structure
- [ ] SUMMARY.md created with one-liner, key findings, and next steps
- [ ] Confidence, dependencies, open questions, and assumptions documented

## SUMMARY.md Requirement

**Create**: `.prompts/060-exception-dispatcher-research/SUMMARY.md`

Required sections:
- **One-liner**: Substantive summary (not generic "research completed")
- **Version**: v1
- **Key Findings**: Top 3-5 actionable discoveries
- **Decisions Needed**: Questions requiring user input before planning
- **Blockers**: External impediments (if any)
- **Next Step**: "Create planning prompt (061-exception-dispatcher-plan)"

---

**Execution notes**: Use extended thinking for complex analysis. Read files using Read tool (not bash cat). Use Grep to find patterns across codebase. Create quality report distinguishing verified from assumed findings.
