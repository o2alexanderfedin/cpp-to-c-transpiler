# C++23 Feature Support Gaps Analysis

<gaps-analysis>
  <metadata>
    <document-type>Comprehensive Gaps Analysis</document-type>
    <transpiler>cpptoc C++ to C Transpiler</transpiler>
    <analysis-date>2025-12-24</analysis-date>
    <scope>Phases 1-6 C++23 Features + Phase 33 Validation Suite</scope>
    <methodology>Code review, test execution, documentation analysis, AST inspection</methodology>
  </metadata>

  <summary>
    <key-finding>Header file skipping is the #1 blocker, affecting ~70% of C++23 tests</key-finding>
    <test-statistics>
      <total-tests>1599</total-tests>
      <phase-1-6-tests>80</phase-1-6-tests>
      <phase-1-6-passing>70</phase-1-6-passing>
      <phase-1-6-failing>10</phase-1-6-failing>
      <phase-1-6-pass-rate>87.5%</phase-1-6-pass-rate>
      <phase-33-tests>130</phase-33-tests>
      <phase-33-pass-rate>0.0%</phase-33-pass-rate>
      <actual-cpp23-coverage>10-12%</actual-cpp23-coverage>
    </test-statistics>
    <critical-gaps>
      <gap priority="1">Header file skipping prevents transpilation of C++23 test suite</gap>
      <gap priority="2">Phase 4 API blocker (Clang 17 vs Clang 18+ required)</gap>
      <gap priority="3">CTAD inherited constructors (P2582R1) completely unimplemented</gap>
      <gap priority="4">Runtime fallback for constexpr/consteval loses optimization</gap>
      <gap priority="5">No integration testing - Phase 1-6 features untested in real C++23 code</gap>
    </critical-gaps>
  </summary>

  <category name="API and Tooling Blockers">
    <blocker>
      <name>Clang API Version Mismatch - Phase 4</name>
      <severity>HIGH</severity>
      <affected-features>
        <feature>Deducing this / Explicit Object Parameters (P0847R7)</feature>
      </affected-features>
      <description>
        Phase 4 implementation is complete with all infrastructure, but blocked by missing
        `isExplicitObjectMemberFunction()` API in current Clang 17. This API was introduced
        in Clang 18+.
      </description>
      <impact>
        <tests-blocked>10/12 DeducingThisTranslatorTest tests</tests-blocked>
        <user-facing-impact>
          Phase 4 feature (deducing this) is completely non-functional. Users cannot transpile
          any C++23 code using explicit object parameters, one of the most impactful C++23 features.
        </user-facing-impact>
      </impact>
      <current-state>
        - ✅ DeducingThisTranslator class implemented (326 lines)
        - ✅ 12 comprehensive tests written
        - ✅ Integration with CppToCVisitor complete
        - ❌ API unavailable: `isExplicitObjectMemberFunction()` missing
        - ⚠️ 2/12 tests passing (logic-only tests, no AST dependency)
        - ❌ 10/12 tests failing (require AST API)
      </current-state>
      <workaround>
        <option>None available without Clang upgrade</option>
        <option>Feature flag to detect and warn users</option>
        <option>Manual code refactoring (expand deducing this to separate methods)</option>
      </workaround>
      <resolution>
        <timeline>Blocked until system upgrade to Clang 18+</timeline>
        <action>Upgrade LLVM/Clang: `brew upgrade llvm` or use newer installation</action>
        <auto-activate>No code changes needed - will activate automatically on upgrade</auto-activate>
      </resolution>
      <references>
        <doc>PHASE_4_IMPLEMENTATION_NOTE.md</doc>
        <proposal>P0847R7: Deducing this</proposal>
        <clang-docs>https://clang.llvm.org/cxx_status.html</clang-docs>
      </references>
    </blocker>

    <blocker>
      <name>Header File Skipping - Architecture Limitation</name>
      <severity>CRITICAL</severity>
      <affected-features>
        <feature>ALL C++23 features in Phase 33 test suite</feature>
        <feature>Multi-file transpilation</feature>
        <feature>Library code transpilation</feature>
      </affected-features>
      <description>
        CppToCVisitor systematically skips ALL declarations from included headers using
        `isInMainFile()` checks (12 locations in CppToCVisitor.cpp). This was designed
        for single-file transpilation but catastrophically blocks Phase 33 validation.
      </description>
      <impact>
        <tests-blocked>~91/130 Phase 33 tests (70%)</tests-blocked>
        <affected-visitors>
          - VisitCXXRecordDecl (line 136)
          - VisitCXXMethodDecl (line 273)
          - VisitCXXConstructorDecl (line 416)
          - VisitCXXDestructorDecl (line 652)
          - VisitFunctionDecl (line 739)
          - VisitCXXMemberCallExpr (line 2765)
          - VisitClassTemplateDecl (line 2885)
          - VisitFunctionTemplateDecl (line 2907)
          - VisitClassTemplateSpecializationDecl (line 2930)
          - VisitAttributedStmt (line 3127)
          - VisitIfStmt (line 3161)
          - VisitCXXFunctionalCastExpr (line 3194)
        </affected-visitors>
        <user-facing-impact>
          - Phase 33 C++23 tests appear to "pass" compilation but produce ZERO output
          - Multi-file projects cannot be transpiled (only main file processed)
          - Library code in headers silently ignored
          - No error messages - silent failure mode
        </user-facing-impact>
      </impact>
      <root-cause>
        Original design assumption: transpiler operates on single .cpp files with all
        code in main file. Phase 33 tests use proper header/implementation separation,
        triggering the skip logic.
      </root-cause>
      <example>
        ```cpp
        // test.h (header file)
        template&lt;typename T&gt;
        class Container {
            T&amp; operator[](int i, int j);  // C++23 multidim subscript
        };

        // test.cpp (main file)
        int main() {
            Container&lt;int&gt; c;
            c[0, 1] = 42;  // Call site transpiled
        }

        // Result: operator[] declaration SKIPPED (in header)
        // Call site transpiled but references non-existent function
        // C compilation fails: undefined reference
        ```
      </example>
      <workaround>
        <option>Inline all code into main file (breaks Phase 33 test structure)</option>
        <option>Disable isInMainFile checks (may cause duplicate symbol issues)</option>
        <option>Implement proper multi-file dependency tracking (Phase 7 work)</option>
      </workaround>
      <resolution>
        <timeline>Phase 7 - Multi-file transpilation architecture</timeline>
        <requirements>
          - Track declaration origin (main file vs header)
          - Generate header/implementation output separately
          - Implement include guard generation
          - Handle cross-file dependencies
          - Preserve declaration order
        </requirements>
        <estimated-effort>Major refactoring - 2-3 weeks</estimated-effort>
      </resolution>
      <immediate-action>
        Document in Phase 33 README as known limitation. Add warning when processing
        files with significant header content.
      </immediate-action>
    </blocker>
  </category>

  <category name="Implementation Limitations - Phase 1-6 Features">
    <limitation>
      <phase>Phase 1</phase>
      <feature>Multidimensional Subscript Operator (P2128R6)</feature>
      <status>COMPLETE</status>
      <test-results>
        <unit-tests>12/12 passing (100%)</unit-tests>
        <integration-tests>0/16 Phase 33 tests (blocked by header skipping)</integration-tests>
      </test-results>
      <documented-limitations>
        <limitation>
          <description>lvalue context detection uses heuristic (const-qualification check)</description>
          <impact>May incorrectly classify some subscript uses as rvalue when they're lvalue</impact>
          <severity>LOW</severity>
          <workaround>Add explicit const-qualification to hint transpiler</workaround>
          <improvement-path>Implement proper parent expression AST analysis (TODO in header)</improvement-path>
        </limitation>
        <limitation>
          <description>No template parameter interaction testing</description>
          <impact>Behavior with template subscript operators unknown</impact>
          <severity>MEDIUM</severity>
          <test-gap>Need tests for: template&lt;typename T&gt; T&amp; operator[](T, T)</test-gap>
        </limitation>
      </documented-limitations>
      <undocumented-issues>
        <issue>
          <found-in>Code review of MultidimSubscriptTranslator.cpp</found-in>
          <description>No handling of rvalue-reference returning subscripts (T&amp;&amp; operator[])</description>
          <use-case-that-fails>Moving from temporary matrix: auto x = std::move(m)[i,j]</use-case-that-fails>
          <fundamental-or-fixable>Fixable - extend getTypeString() to handle rvalue refs</fundamental-or-fixable>
        </issue>
      </undocumented-issues>
      <warnings>
        <warning>No emitWarning calls found - silent failure mode if unhandled case</warning>
      </warnings>
    </limitation>

    <limitation>
      <phase>Phase 2</phase>
      <feature>Static Operators (P1169R4)</feature>
      <status>COMPLETE</status>
      <test-results>
        <unit-tests>10/10 passing (100%)</unit-tests>
        <integration-tests>0/8 Phase 33 tests (blocked by header skipping)</integration-tests>
      </test-results>
      <documented-limitations>
        <limitation>
          <description>Static operators converted to free functions, losing syntax sugar</description>
          <impact>C++ ergonomic call syntax (Matrix::identity[3,3]) becomes C function call</impact>
          <severity>LOW (expected limitation of C)</severity>
          <fundamental>Yes - C has no static member operators</fundamental>
        </limitation>
      </documented-limitations>
      <undocumented-issues>
        <issue>
          <found-in>StaticOperatorTranslatorTest.cpp review</found-in>
          <description>No tests for static operator+ or other arithmetic operators</description>
          <test-gap>Only tests operator() and operator[] - missing +, -, *, /, etc.</test-gap>
          <fundamental-or-fixable>Fixable - same pattern applies to all operators</fundamental-or-fixable>
        </issue>
      </undocumented-issues>
      <warnings>
        <warning>No emitWarning calls - user unaware when static operator encountered</warning>
      </warnings>
    </limitation>

    <limitation>
      <phase>Phase 3</phase>
      <feature>[[assume]] Attribute (P1774R8)</feature>
      <status>COMPLETE</status>
      <test-results>
        <unit-tests>12/12 passing (100%)</unit-tests>
        <integration-tests>0/13 Phase 33 tests (blocked by header skipping)</integration-tests>
      </test-results>
      <documented-limitations>
        <limitation>
          <description>Three strategies available: Strip, Comment, Builtin</description>
          <impact>User must choose strategy - no auto-detection of compiler capabilities</impact>
          <severity>LOW</severity>
          <workaround>Default to Strip strategy for maximum compatibility</workaround>
        </limitation>
        <limitation>
          <description>Builtin strategy uses __builtin_assume (GCC/Clang specific)</description>
          <impact>Not portable to all C compilers</impact>
          <severity>MEDIUM</severity>
          <improvement-path>Add compiler detection and fallback strategy</improvement-path>
        </limitation>
      </documented-limitations>
      <undocumented-issues>
        <issue>
          <found-in>AssumeAttributeHandler.h</found-in>
          <description>No handling of nested attributes or complex attribute combinations</description>
          <use-case-that-fails>[[assume(x &gt; 0), nodiscard]] statement;</use-case-that-fails>
          <fundamental-or-fixable>Fixable - extend attribute parsing logic</fundamental-or-fixable>
        </issue>
      </undocumented-issues>
      <warnings>
        <warning>No emitWarning when assume attribute stripped - silent loss of optimization</warning>
      </warnings>
    </limitation>

    <limitation>
      <phase>Phase 4</phase>
      <feature>Deducing This / Explicit Object Parameters (P0847R7)</feature>
      <status>BLOCKED BY API</status>
      <test-results>
        <unit-tests>2/12 passing (16.7% - only non-AST tests)</unit-tests>
        <integration-tests>N/A (no Phase 33 deducing-this category)</integration-tests>
      </test-results>
      <documented-limitations>
        <limitation>
          <description>Requires Clang 18+ API: isExplicitObjectMemberFunction()</description>
          <impact>Entire feature non-functional on Clang 17 systems</impact>
          <severity>CRITICAL (blocks feature completely)</severity>
          <resolution>System upgrade to Clang 18+</resolution>
        </limitation>
      </documented-limitations>
      <test-failures>
        <failure>
          <test>AutoRefGenerates2Overloads</test>
          <reason>Cannot detect explicit object parameter without API</reason>
          <expected>2 overloads (lvalue, const) generated</expected>
          <actual>0 overloads - method not recognized as deducing-this</actual>
        </failure>
        <failure>
          <test>AutoRefRefGenerates4Overloads</test>
          <reason>Forwarding reference detection impossible</reason>
          <expected>4 overloads (lvalue, const, rvalue, const-rvalue)</expected>
          <actual>0 overloads</actual>
        </failure>
        <failure-pattern>All 10 failing tests have same root cause: API unavailable</failure-pattern>
      </test-failures>
      <undocumented-issues>
        <issue>
          <found-in>DeducingThisTranslator.h line 244</found-in>
          <description>TODO: "Phase 2: Implement proper parent expression analysis"</description>
          <impact>Even with API, context detection may be incomplete</impact>
          <fundamental-or-fixable>Fixable but complex - requires AST traversal up to parent</fundamental-or-fixable>
        </issue>
      </undocumented-issues>
      <future-work>
        When API becomes available:
        1. Enable detection in VisitCXXMethodDecl
        2. Verify overload expansion logic
        3. Test call site qualifier analysis
        4. Add integration tests with Phase 33 when deducing-this tests available
      </future-work>
    </limitation>

    <limitation>
      <phase>Phase 5</phase>
      <feature>if consteval (P1938R3)</feature>
      <status>COMPLETE (with runtime fallback)</status>
      <test-results>
        <unit-tests>12/12 passing (100%)</unit-tests>
        <integration-tests>0/13 Phase 33 tests (blocked by header skipping)</integration-tests>
      </test-results>
      <documented-limitations>
        <limitation>
          <description>Always selects runtime (else) branch - conservative strategy</description>
          <impact>Loses compile-time optimization opportunities</impact>
          <severity>MEDIUM (correctness preserved, performance lost)</severity>
          <fundamental>Partial - transpiler cannot execute consteval code at transpile-time</fundamental>
        </limitation>
        <limitation>
          <description>Optimistic strategy not implemented (Both strategy also unimplemented)</description>
          <impact>Cannot leverage compile-time context detection for better code</impact>
          <severity>LOW</severity>
          <improvement-path>Implement analyzeContext() heuristics for constexpr functions</improvement-path>
        </limitation>
      </documented-limitations>
      <warnings-found>
        <warning-call location="ConstevalIfTranslator.cpp:42">
          <message>"if consteval: using runtime path (C has no consteval)"</message>
          <strategy>Runtime (default)</strategy>
          <frequency>Every if consteval statement</frequency>
        </warning-call>
        <warning-call location="ConstevalIfTranslator.cpp:51">
          <message>"if consteval: using compile-time path"</message>
          <strategy>Optimistic (when context detected)</strategy>
          <note>Dead code - Optimistic strategy not implemented</note>
        </warning-call>
        <warning-call location="ConstevalIfTranslator.cpp:63">
          <message>"if consteval: Both strategy not implemented, using runtime path"</message>
          <strategy>Both</strategy>
          <note>Documents missing feature</note>
        </warning-call>
        <warning-call location="ConstevalIfTranslator.cpp:70">
          <message>"if consteval: no runtime branch available, statement removed"</message>
          <strategy>All</strategy>
          <severity>HIGH - code deleted silently</severity>
        </warning-call>
      </warnings-found>
      <undocumented-issues>
        <issue>
          <found-in>ConstevalIfTranslator.h line 16</found-in>
          <description>Both strategy requires preprocessor (#ifdef) - not implemented</description>
          <impact>Cannot generate dual-path code for manual selection</impact>
          <fundamental-or-fixable>Fixable - emit preprocessor directives in C output</fundamental-or-fixable>
        </issue>
      </undocumented-issues>
      <user-facing-impact>
        Users see warnings for EVERY if consteval, which may be noisy in codebases
        with heavy constexpr usage. Consider adding --suppress-consteval-warnings flag.
      </user-facing-impact>
    </limitation>

    <limitation>
      <phase>Phase 6</phase>
      <feature>auto(x) Decay-Copy (P0849R8)</feature>
      <status>COMPLETE</status>
      <test-results>
        <unit-tests>12/12 passing (100%)</unit-tests>
        <integration-tests>0/22 Phase 33 tests (blocked by header skipping)</integration-tests>
      </test-results>
      <documented-limitations>
        <limitation>
          <description>auto{x} treated identically to auto(x) - no direct-initialization distinction</description>
          <impact>Semantic difference between () and {} initialization lost</impact>
          <severity>LOW (rarely matters in practice)</severity>
          <fundamental>Partial - C has no initialization syntax distinction</fundamental>
        </limitation>
        <limitation>
          <description>Class-type copy constructors require runtime library</description>
          <impact>Cannot decay-copy user-defined types without runtime support</impact>
          <severity>MEDIUM</severity>
          <improvement-path>Generate copy constructor calls in C output</improvement-path>
        </limitation>
        <limitation>
          <description>Template parameter decay not fully supported</description>
          <impact>auto(template_param) may fail in template contexts</impact>
          <severity>MEDIUM</severity>
          <test-gap>Need tests for template interaction</test-gap>
        </limitation>
      </documented-limitations>
      <undocumented-issues>
        <issue>
          <found-in>AutoDecayCopyTranslator.cpp code review</found-in>
          <description>No handling of volatile-qualified types (in addition to const)</description>
          <use-case-that-fails>volatile int&amp; vref; auto copy = auto(vref);</use-case-that-fails>
          <fundamental-or-fixable>Fixable - extend decay rules to strip volatile</fundamental-or-fixable>
          <test-exists>VolatileReferenceToValue test exists and passes - issue may be theoretical</test-exists>
        </issue>
      </undocumented-issues>
      <warnings>
        <warning>No emitWarning calls - silent fallback for unsupported cases</warning>
      </warnings>
    </limitation>

    <limitation>
      <phase>Phase 6</phase>
      <feature>Constexpr Enhancements (Partial)</feature>
      <status>COMPLETE (with runtime fallback)</status>
      <test-results>
        <unit-tests>10/10 passing (100%)</unit-tests>
        <integration-tests>0/19 Phase 33 tests (blocked by header skipping)</integration-tests>
      </test-results>
      <documented-limitations>
        <limitation>
          <description>Only simple cases evaluated at compile-time (return literal/expression)</description>
          <impact>Complex constexpr functions fall back to runtime execution</impact>
          <severity>MEDIUM (correctness OK, performance loss)</severity>
          <fundamental>Yes - transpiler cannot execute arbitrary C++ code</fundamental>
        </limitation>
        <limitation>
          <description>Parameters, loops, control flow → runtime fallback</description>
          <impact>Most real-world constexpr functions run at runtime</impact>
          <severity>MEDIUM</severity>
          <acceptable>Yes - Phase 6 goal was coverage, not full compile-time execution</acceptable>
        </limitation>
        <limitation>
          <description>No consteval support (immediate functions)</description>
          <impact>consteval functions transpiled as regular functions (incorrect semantics)</impact>
          <severity>HIGH (semantic mismatch)</severity>
          <workaround>Warn user to manually inline consteval functions</workaround>
        </limitation>
      </documented-limitations>
      <warnings>
        <warning>No emitWarning when constexpr function falls back to runtime</warning>
        <warning>User cannot distinguish compile-time vs runtime code generation</warning>
      </warnings>
      <undocumented-issues>
        <issue>
          <found-in>PHASE_6_AUTO_DECAY_CONSTEXPR.md line 118-120</found-in>
          <description>Claims "acceptable partial support" but doesn't quantify coverage</description>
          <impact>Users don't know which constexpr patterns work vs fail</impact>
          <improvement-path>Document supported constexpr patterns explicitly</improvement-path>
        </issue>
      </undocumented-issues>
    </limitation>
  </category>

  <category name="Unimplemented Features from Original Plan">
    <feature>
      <name>Class Template Argument Deduction with Inherited Constructors (P2582R1)</name>
      <proposal>P2582R1</proposal>
      <status>NOT IMPLEMENTED</status>
      <original-plan-position>Feature #8 of Phase 1-6 plan</original-plan-position>
      <phase-33-tests>10 tests in class-template-deduction-inherited/ category</phase-33-tests>
      <current-state>
        - ❌ No CTADInheritedTranslator class
        - ❌ No source files
        - ❌ No tests
        - ❌ No integration with CppToCVisitor
        - ⚠️ Basic CTAD works (from earlier implementation)
        - ❌ Inherited constructor cases fail
      </current-state>
      <complexity-estimate>
        <level>HIGH</level>
        <reasoning>
          Requires understanding inheritance graph, constructor forwarding,
          and template argument deduction rules. More complex than Phases 1-3.
        </reasoning>
        <estimated-effort>1-2 weeks</estimated-effort>
      </complexity-estimate>
      <user-demand>
        <level>MEDIUM</level>
        <reasoning>
          CTAD is convenient but not critical. Inheritance cases are edge cases.
          Most users can work around with explicit template arguments.
        </reasoning>
      </user-demand>
      <phase-7-candidate>
        <priority>MEDIUM</priority>
        <reasoning>
          Good incremental feature - extends existing CTAD support.
          Would increase Phase 33 pass rate. Clear implementation path.
        </reasoning>
        <prerequisites>
          - Fix header file skipping first (otherwise tests remain blocked)
          - Study Clang's DeductionGuide infrastructure
          - Implement inherited constructor detection
        </prerequisites>
      </phase-7-candidate>
      <example>
        ```cpp
        // C++23 P2582R1 example
        template&lt;typename T&gt;
        struct Base {
            Base(T value);
        };

        template&lt;typename T&gt;
        struct Derived : Base&lt;T&gt; {
            using Base&lt;T&gt;::Base;  // Inherit constructor
        };

        Derived d(42);  // CTAD: deduces Derived&lt;int&gt; from inherited constructor
        // Currently fails - requires explicit: Derived&lt;int&gt; d(42);
        ```
      </example>
    </feature>

    <feature>
      <name>Ranges Enhancements (P2678R0)</name>
      <proposal>P2678R0</proposal>
      <status>NOT IMPLEMENTED (and likely never will be)</status>
      <phase-33-tests>10 tests in ranges-P2678/ category</phase-33-tests>
      <current-state>
        - ❌ No ranges support
        - ❌ Requires full STL transpilation
        - ❌ Architectural limitation - ranges are library, not language
      </current-state>
      <complexity-estimate>
        <level>EXTREMELY HIGH</level>
        <reasoning>
          Ranges are C++20 library features requiring massive STL infrastructure.
          Would need to transpile &lt;ranges&gt;, &lt;iterator&gt;, &lt;algorithm&gt;, concepts, etc.
        </reasoning>
        <estimated-effort>Months (not weeks)</estimated-effort>
      </complexity-estimate>
      <user-demand>
        <level>LOW for transpiler</level>
        <reasoning>
          Users porting C++ to C typically avoid STL-heavy code.
          Ranges are modern C++ idioms incompatible with C translation goals.
        </reasoning>
      </user-demand>
      <phase-7-candidate>
        <priority>VERY LOW / NOT RECOMMENDED</priority>
        <reasoning>
          Out of scope for C transpilation. Better to document as limitation
          and suggest manual refactoring to C-compatible patterns.
        </reasoning>
        <alternative>
          Document ranges as unsupported. Provide migration guide showing
          how to refactor ranges-based code to traditional loops.
        </alternative>
      </phase-7-candidate>
      <architectural-blocker>
        Ranges fundamentally rely on:
        - Concepts (no C equivalent)
        - Template metaprogramming (limited support)
        - Iterator protocols (C has no standard)
        - Lazy evaluation (C has no generators/coroutines)
        - STL containers (not transpiled)
      </architectural-blocker>
    </feature>

    <feature>
      <name>Miscellaneous C++23 Features</name>
      <proposal>Various</proposal>
      <status>MIXED</status>
      <phase-33-tests>19 tests in miscellaneous/ category</phase-33-tests>
      <breakdown>
        <subfeature>
          <name>Labels at end of statements (P2324R0)</name>
          <status>UNTESTED - may work already</status>
          <complexity>LOW - likely just needs testing</complexity>
        </subfeature>
        <subfeature>
          <name>Literal suffix improvements</name>
          <status>UNKNOWN</status>
          <complexity>LOW</complexity>
        </subfeature>
        <subfeature>
          <name>Decay copy in language (P0849R8)</name>
          <status>✅ IMPLEMENTED (Phase 6)</status>
        </subfeature>
        <subfeature>
          <name>Other minor language features</name>
          <status>NEEDS CATEGORIZATION</status>
          <action>Review miscellaneous/ test files to identify specific features</action>
        </subfeature>
      </breakdown>
      <recommendation>
        Audit miscellaneous/ tests individually. Some may already work,
        others may be quick wins for Phase 7.
      </recommendation>
    </feature>
  </category>

  <category name="Architecture Gaps">
    <gap>
      <name>Header File Skipping - Critical Architecture Issue</name>
      <description>See API/Tooling Blockers section above</description>
      <impact>70% of Phase 33 tests</impact>
      <estimated-affected-percentage>~91/130 tests blocked</estimated-affected-percentage>
      <resolution>Phase 7 multi-file transpilation redesign</resolution>
    </gap>

    <gap>
      <name>No Integration Testing of Phase 1-6 Features</name>
      <severity>HIGH</severity>
      <description>
        Phase 1-6 features pass unit tests (70/80 = 87.5%) but have 0% integration
        test pass rate due to header skipping. This means:
        - Multidim subscript works in isolation but not in real C++23 code
        - Static operators work in unit tests but not in Phase 33 suite
        - [[assume]] attribute handling untested in real code
        - auto(x) decay-copy untested with templates/complex types
        - constexpr fallback behavior unverified in production scenarios
      </description>
      <risk>
        Features may have edge cases or interactions not caught by unit tests.
        Unit test success gives false confidence.
      </risk>
      <mitigation>
        <immediate>Document gap in Phase 33 summary</immediate>
        <short-term>Create standalone integration tests that bypass header skipping</short-term>
        <long-term>Fix header skipping, rerun Phase 33 validation</long-term>
      </mitigation>
    </gap>

    <gap>
      <name>AST Replacement Infrastructure Incomplete</name>
      <severity>MEDIUM</severity>
      <description>
        Phase 1-6 translators generate C AST nodes but some don't have proper
        replacement mechanisms. Example: MultidimSubscriptTranslator returns
        CallExpr but parent expression may not be replaced in C_TranslationUnit.
      </description>
      <evidence>
        Code review shows `transform()` methods return new AST nodes, but
        caller responsibility for replacement varies. No consistent pattern.
      </evidence>
      <impact>
        - Generated C code may contain C++ nodes
        - AST dumping shows mixed C++/C tree
        - Potential for invalid C output
      </impact>
      <status>
        Needs systematic audit of all Phase 1-6 translators to verify
        AST node replacement actually occurs.
      </status>
    </gap>

    <gap>
      <name>Template Interaction Testing Missing</name>
      <severity>MEDIUM</severity>
      <description>
        No tests verify Phase 1-6 features interact correctly with templates. Examples:
        - Multidim subscript on template class: `template&lt;typename T&gt; class Matrix { T&amp; operator[](int,int); }`
        - Static operator in template: `template&lt;typename T&gt; struct Wrapper { static T operator()(); }`
        - auto(x) with template parameter: `template&lt;typename T&gt; void f(T&amp;&amp; x) { auto copy = auto(x); }`
      </description>
      <risk>
        Template monomorphization (Phase 32) may not preserve C++23 feature transformations.
        Generated code may have C++ syntax in monomorphized instances.
      </risk>
      <test-gap>
        Add template interaction tests for each Phase 1-6 feature before Phase 7.
      </test-gap>
    </gap>

    <gap>
      <name>Type System Limitations for C++23 Features</name>
      <severity>MEDIUM</severity>
      <description>
        C++23 features often interact with advanced type system features not
        fully supported by transpiler:
        - auto return type deduction (partial support)
        - decltype in complex contexts (limited)
        - Template argument deduction (CTAD incomplete)
        - Reference collapsing (untested)
        - Perfect forwarding (limited to simple cases)
      </description>
      <example>
        ```cpp
        // C++23 deducing this with auto return
        struct Container {
            auto&amp;&amp; get(this auto&amp;&amp; self, int i) {
                return std::forward&lt;decltype(self)&gt;(self).data[i];
            }
        };
        // Requires: deducing this (Phase 4) + auto&amp;&amp; return + decltype + forwarding
        // Current support: NONE of these work together
        ```
      </example>
      <impact>
        Real-world C++23 code uses features in combination. Single-feature
        support insufficient for actual migration use cases.
      </impact>
    </gap>
  </category>

  <category name="Test Analysis - Phase 1-6 Unit Tests">
    <test-suite>
      <name>Phase 1-6 C++23 Features</name>
      <total-tests>80</total-tests>
      <passing>70</passing>
      <failing>10</failing>
      <pass-rate>87.5%</pass-rate>
    </test-suite>

    <failure-group>
      <name>Phase 4 - Deducing This (API Blocked)</name>
      <count>10 tests</count>
      <root-cause>Clang 17 missing isExplicitObjectMemberFunction() API</root-cause>
      <failing-tests>
        <test>AutoRefGenerates2Overloads</test>
        <test>ConstAutoRefGenerates1Overload</test>
        <test>AutoRefRefGenerates4Overloads</test>
        <test>AutoValueGenerates1Overload</test>
        <test>CallOnLvalueObject</test>
        <test>CallOnConstLvalueObject</test>
        <test>CallOnRvalueObject</test>
        <test>MethodWithAdditionalParameters</test>
        <test>MethodReturnsValueUsingSelf</test>
        <test>MultipleDeducingThisMethods</test>
      </failing-tests>
      <commonality>All require AST detection of explicit object parameters</commonality>
      <expected-vs-unexpected>100% expected - documented in PHASE_4_IMPLEMENTATION_NOTE.md</expected-vs-unexpected>
      <resolution-path>
        1. Upgrade to Clang 18+ (brew upgrade llvm)
        2. No code changes needed
        3. Tests will auto-pass when API available
      </resolution-path>
    </failure-group>

    <test-results-by-phase>
      <phase number="1" name="Multidimensional Subscript">
        <total>12</total>
        <passing>12</passing>
        <failing>0</failing>
        <pass-rate>100%</pass-rate>
        <status>✅ COMPLETE</status>
      </phase>
      <phase number="2" name="Static Operators">
        <total>10</total>
        <passing>10</passing>
        <failing>0</failing>
        <pass-rate>100%</pass-rate>
        <status>✅ COMPLETE</status>
      </phase>
      <phase number="3" name="[[assume]] Attribute">
        <total>12</total>
        <passing>12</passing>
        <failing>0</failing>
        <pass-rate>100%</pass-rate>
        <status>✅ COMPLETE</status>
      </phase>
      <phase number="4" name="Deducing This">
        <total>12</total>
        <passing>2</passing>
        <failing>10</failing>
        <pass-rate>16.7%</pass-rate>
        <status>⚠️ API BLOCKED</status>
        <note>2 passing tests are logic-only (QualifierSuffixGeneration, NonExplicitObjectMethodReturnsEmpty)</note>
      </phase>
      <phase number="5" name="if consteval">
        <total>12</total>
        <passing>12</passing>
        <failing>0</failing>
        <pass-rate>100%</pass-rate>
        <status>✅ COMPLETE (runtime fallback)</status>
      </phase>
      <phase number="6a" name="auto(x) Decay-Copy">
        <total>12</total>
        <passing>12</passing>
        <failing>0</failing>
        <pass-rate>100%</pass-rate>
        <status>✅ COMPLETE</status>
      </phase>
      <phase number="6b" name="Constexpr Enhancements">
        <total>10</total>
        <passing>10</passing>
        <failing>0</failing>
        <pass-rate>100%</pass-rate>
        <status>✅ COMPLETE (partial)</status>
      </phase>
    </test-results-by-phase>
  </category>

  <category name="Test Analysis - Phase 33 Integration Tests">
    <test-suite>
      <name>Phase 33 C++23 Validation Suite (GCC-adapted)</name>
      <total-tests>130</total-tests>
      <passing>0</passing>
      <failing>130</failing>
      <pass-rate>0.0%</pass-rate>
      <primary-blocker>Header file skipping</primary-blocker>
    </test-suite>

    <category-breakdown>
      <category name="if-consteval-P1938">
        <tests>13</tests>
        <status>0% pass</status>
        <blocker>Header skipping (11 tests) + Runtime fallback limitation (2 tests)</blocker>
        <phase-implementation>Phase 5</phase-implementation>
        <unit-test-pass-rate>100% (12/12)</unit-test-pass-rate>
        <gap>Integration vs unit test discrepancy</gap>
      </category>
      <category name="multidim-subscript-P2128">
        <tests>16</tests>
        <status>0% pass</status>
        <blocker>Header skipping (all 16 tests)</blocker>
        <phase-implementation>Phase 1</phase-implementation>
        <unit-test-pass-rate>100% (12/12)</unit-test-pass-rate>
        <gap>Integration completely untested despite unit test success</gap>
      </category>
      <category name="static-operators-P1169">
        <tests>8</tests>
        <status>0% pass</status>
        <blocker>Header skipping (all 8 tests)</blocker>
        <phase-implementation>Phase 2</phase-implementation>
        <unit-test-pass-rate>100% (10/10)</unit-test-pass-rate>
        <gap>Zero validation of real-world usage</gap>
      </category>
      <category name="auto-deduction-P0849">
        <tests>22</tests>
        <status>0% pass (untested)</status>
        <blocker>Header skipping (estimated 18 tests) + No implementation (4 tests)</blocker>
        <phase-implementation>Phase 6a (auto(x) decay-copy)</phase-implementation>
        <unit-test-pass-rate>100% (12/12)</unit-test-pass-rate>
        <note>Category broader than Phase 6a scope - includes auto deduction generally</note>
      </category>
      <category name="constexpr-enhancements">
        <tests>19</tests>
        <status>0% pass</status>
        <blocker>Header skipping (12 tests) + Constexpr evaluation limitation (7 tests)</blocker>
        <phase-implementation>Phase 6b (partial constexpr)</phase-implementation>
        <unit-test-pass-rate>100% (10/10)</unit-test-pass-rate>
        <gap>Unit tests focus on simple cases, integration tests have complex constexpr</gap>
      </category>
      <category name="class-template-deduction-inherited">
        <tests>10</tests>
        <status>0% pass</status>
        <blocker>Header skipping (6 tests) + Feature not implemented (4 tests)</blocker>
        <phase-implementation>NOT IMPLEMENTED (was planned Feature #8)</phase-implementation>
        <unit-test-pass-rate>N/A (no tests)</unit-test-pass-rate>
        <priority>MEDIUM for Phase 7</priority>
      </category>
      <category name="attributes-P2180">
        <tests>13</tests>
        <status>0% pass (untested)</status>
        <blocker>Header skipping (all 13 tests)</blocker>
        <phase-implementation>Phase 3 ([[assume]] only)</phase-implementation>
        <unit-test-pass-rate>100% for [[assume]] (12/12)</unit-test-pass-rate>
        <note>P2180 covers multiple attributes, Phase 3 only implemented [[assume]]</note>
        <other-attributes>[[nodiscard]], [[deprecated]], etc. - status unknown</other-attributes>
      </category>
      <category name="ranges-P2678">
        <tests>10</tests>
        <status>0% pass</status>
        <blocker>Architectural - requires full STL transpilation</blocker>
        <phase-implementation>NOT IMPLEMENTED (not planned)</phase-implementation>
        <unit-test-pass-rate>N/A</unit-test-pass-rate>
        <recommendation>Document as unsupported, provide migration guide</recommendation>
      </category>
      <category name="miscellaneous">
        <tests>19</tests>
        <status>0% pass (mixed blockers)</status>
        <blocker>Header skipping + varies by test</blocker>
        <phase-implementation>MIXED (some implemented, some not)</phase-implementation>
        <action-needed>Audit tests individually to categorize</action-needed>
      </category>
    </category-breakdown>

    <estimated-pass-rate-after-header-fix>
      <scenario>If header skipping fixed</scenario>
      <conservative-estimate>15-20%</conservative-estimate>
      <breakdown>
        - Phase 1 (multidim subscript): 12-14/16 tests (75-85%)
        - Phase 2 (static operators): 6-7/8 tests (75-85%)
        - Phase 3 ([[assume]]): 10-11/13 tests (75-85%)
        - Phase 5 (if consteval): 8-10/13 tests (60-75% - runtime fallback limitation)
        - Phase 6a (auto(x)): 8-12/22 tests (35-55% - category broader than feature)
        - Phase 6b (constexpr): 5-8/19 tests (25-40% - complex constexpr fails)
        - CTAD inherited: 0/10 tests (not implemented)
        - Attributes: 5-8/13 tests (40-60% - only [[assume]] implemented)
        - Ranges: 0/10 tests (architectural blocker)
        - Miscellaneous: 5-10/19 tests (25-50% - varies)
        Total: 59-90/130 tests = 45-69% (midpoint ~57%)
      </breakdown>
      <optimistic-estimate>25-30% (if Phase 4 API available too)</optimistic-estimate>
    </estimated-pass-rate-after-header-fix>
  </category>

  <category name="Documentation Gaps">
    <gap>
      <name>User-Facing Feature Support Matrix Missing</name>
      <severity>HIGH</severity>
      <description>
        No single document tells users "what C++23 features work" in practical terms.
        FEATURE-MATRIX.md exists but shows 0% for everything (baseline not updated).
      </description>
      <impact>
        Users don't know if transpiler can handle their C++23 code. Must guess or test.
      </impact>
      <recommendation>
        Update FEATURE-MATRIX.md with actual Phase 1-6 implementation status:
        - Multidim subscript: ✅ SUPPORTED (with limitations)
        - Static operators: ✅ SUPPORTED
        - [[assume]]: ✅ SUPPORTED (3 strategies)
        - Deducing this: ⚠️ BLOCKED (API requirement)
        - if consteval: ⚠️ PARTIAL (runtime fallback)
        - auto(x): ✅ SUPPORTED (simple cases)
        - constexpr enhancements: ⚠️ PARTIAL (simple cases)
      </recommendation>
    </gap>

    <gap>
      <name>Limitations Not User-Accessible</name>
      <severity>MEDIUM</severity>
      <description>
        Limitations documented in header files (e.g., MultidimSubscriptTranslator.h line 244
        TODO) but not in user documentation. Users won't read source code.
      </description>
      <recommendation>
        Create LIMITATIONS.md in docs/ with:
        - Known edge cases per feature
        - Workarounds
        - Examples that fail
        - When to use manual refactoring
      </recommendation>
    </gap>

    <gap>
      <name>Migration Guide Missing</name>
      <severity>MEDIUM</severity>
      <description>
        No guide for users porting C++23 code to C. Should explain:
        - Which C++23 features transpile automatically
        - Which require refactoring
        - How to work around unsupported features
        - Best practices for transpiler-friendly C++
      </description>
      <recommendation>
        Create docs/CPP23_MIGRATION_GUIDE.md with practical advice.
      </recommendation>
    </gap>

    <gap>
      <name>Warning Messages Not Documented</name>
      <severity>LOW</severity>
      <description>
        ConstevalIfTranslator emits warnings but they're not documented.
        Users don't know what warnings mean or how to suppress them.
      </description>
      <recommendation>
        Document all warning messages in docs/WARNINGS.md with explanations
        and suppression flags.
      </recommendation>
    </gap>
  </category>

  <recommendations>
    <immediate-actions priority="CRITICAL">
      <action>
        <title>Fix Header File Skipping (Phase 7)</title>
        <impact>Unblocks 70% of Phase 33 tests</impact>
        <effort>2-3 weeks (major refactoring)</effort>
        <approach>
          1. Remove or parameterize isInMainFile() checks
          2. Implement file origin tracking (main vs header)
          3. Generate separate .h and .c outputs
          4. Add include guard generation
          5. Handle cross-file dependencies
          6. Preserve declaration order
        </approach>
        <priority>1 - Highest impact per effort</priority>
      </action>

      <action>
        <title>Update User Documentation</title>
        <impact>Sets realistic user expectations</impact>
        <effort>1-2 days</effort>
        <files-to-update>
          - tests/real-world/cpp23-validation/docs/FEATURE-MATRIX.md (update with Phase 1-6 status)
          - README.md (add C++23 support section)
          - Create docs/CPP23_LIMITATIONS.md
          - Create docs/CPP23_MIGRATION_GUIDE.md
        </files-to-update>
        <priority>2 - Low effort, high user value</priority>
      </action>

      <action>
        <title>Add Integration Tests Bypassing Header Skipping</title>
        <impact>Validates Phase 1-6 features work in real code</impact>
        <effort>2-3 days</effort>
        <approach>
          Create tests/integration/cpp23/ with single-file tests (all code in .cpp,
          no headers) for each Phase 1-6 feature. Verify AST replacement works end-to-end.
        </approach>
        <priority>3 - Risk mitigation</priority>
      </action>
    </immediate-actions>

    <short-term-phase-7-candidates>
      <candidate>
        <feature>CTAD with Inherited Constructors (P2582R1)</feature>
        <priority>HIGH</priority>
        <rationale>
          - Completes original Phase 1-6 plan (was Feature #8)
          - 10 tests in Phase 33 suite
          - Clear implementation path
          - Extends existing CTAD infrastructure
        </rationale>
        <prerequisites>Header skipping fixed first</prerequisites>
        <estimated-effort>1-2 weeks</estimated-effort>
      </candidate>

      <candidate>
        <feature>Template Interaction Testing for Phase 1-6</feature>
        <priority>MEDIUM-HIGH</priority>
        <rationale>
          - Risk mitigation - verify features work with templates
          - May discover bugs in monomorphization interaction
          - Low effort (just tests, no new features)
        </rationale>
        <estimated-effort>3-5 days</estimated-effort>
      </candidate>

      <candidate>
        <feature>Improved Constexpr Evaluation</feature>
        <priority>MEDIUM</priority>
        <rationale>
          - Current runtime fallback loses performance
          - Can incrementally expand supported patterns
          - High user value (constexpr common in modern C++)
        </rationale>
        <approach>
          Leverage Clang's APValue evaluator more aggressively.
          Support loops, control flow, parameters in simple cases.
        </approach>
        <estimated-effort>2-3 weeks</estimated-effort>
      </candidate>

      <candidate>
        <feature>Miscellaneous C++23 Features Audit</feature>
        <priority>MEDIUM</priority>
        <rationale>
          - 19 tests in miscellaneous/ - some may be easy wins
          - Could boost pass rate significantly
          - Low-hanging fruit identification
        </rationale>
        <approach>
          1. Categorize all 19 tests by feature
          2. Identify which already work (just need testing)
          3. Implement quick wins (< 2 days each)
        </approach>
        <estimated-effort>1 week (audit) + varies per feature</estimated-effort>
      </candidate>
    </short-term-phase-7-candidates>

    <not-recommended>
      <feature>Ranges Support (P2678R0)</feature>
      <reason>Architectural blocker - requires full STL transpilation (months of work)</reason>
      <alternative>Document as unsupported, provide manual refactoring guide</alternative>
    </not-recommended>

    <quality-improvements>
      <improvement>
        <title>Add emitWarning calls to Silent Translators</title>
        <affected>
          - MultidimSubscriptTranslator (no warnings)
          - StaticOperatorTranslator (no warnings)
          - AssumeAttributeHandler (no warnings)
          - AutoDecayCopyTranslator (no warnings)
          - ConstexprEnhancementHandler (no warnings for fallback)
        </affected>
        <benefit>User awareness of feature usage and limitations</benefit>
        <effort>1 day</effort>
      </improvement>

      <improvement>
        <title>Consistent AST Replacement Pattern</title>
        <description>
          Audit all Phase 1-6 translators for proper AST node replacement.
          Verify generated C nodes actually replace C++ nodes in C_TranslationUnit.
        </description>
        <benefit>Ensures valid C output, no mixed C++/C AST</benefit>
        <effort>2-3 days</effort>
      </improvement>

      <improvement>
        <title>Warning Suppression Flags</title>
        <description>
          Add --suppress-consteval-warnings, --suppress-assume-warnings, etc.
          for users who understand limitations but don't want noisy output.
        </description>
        <benefit>Better user experience for production use</benefit>
        <effort>1 day</effort>
      </improvement>
    </quality-improvements>
  </recommendations>

  <quality-assessment>
    <strengths>
      <strength>
        <title>Phase 1-6 Unit Test Coverage Excellent</title>
        <metric>70/80 tests passing (87.5%)</metric>
        <description>
          Individual features well-tested in isolation. High confidence in
          translator logic correctness.
        </description>
      </strength>

      <strength>
        <title>Clean Architecture - SOLID Principles Followed</title>
        <description>
          Each translator is single-responsibility, follows proven patterns,
          uses CNodeBuilder abstraction. Code is maintainable and extensible.
        </description>
      </strength>

      <strength>
        <title>Comprehensive Documentation in Headers</title>
        <description>
          Each Phase 1-6 header file has excellent documentation: examples,
          translation strategy, architecture notes, references to proposals.
        </description>
      </strength>

      <strength>
        <title>Honest Assessment of Limitations</title>
        <description>
          PHASE_6_AUTO_DECAY_CONSTEXPR.md explicitly states "acceptable partial
          support" with runtime fallback. GAPS.md documents architectural constraints.
          No overpromising.
        </description>
      </strength>
    </strengths>

    <weaknesses>
      <weakness>
        <title>Integration Testing Completely Missing</title>
        <severity>HIGH</severity>
        <metric>0/130 Phase 33 tests passing</metric>
        <description>
          Unit tests pass but no validation of features in real C++23 code.
          Gap between unit test success and integration test failure is enormous.
        </description>
      </weakness>

      <weakness>
        <title>Header File Skipping - Architectural Oversight</title>
        <severity>CRITICAL</severity>
        <description>
          Design assumption (single-file transpilation) baked into 12 visitor
          methods. Blocks entire Phase 33 validation suite. Should have been
          identified earlier.
        </description>
      </weakness>

      <weakness>
        <title>API Dependency Not Checked at Build Time</title>
        <severity>MEDIUM</severity>
        <description>
          Phase 4 fails silently on Clang 17 systems. Should detect Clang version
          at CMake time and either error or disable Phase 4 feature.
        </description>
      </weakness>

      <weakness>
        <title>User Documentation Lags Implementation</title>
        <severity>MEDIUM</severity>
        <description>
          FEATURE-MATRIX.md shows 0% for all features despite Phase 1-6
          implementations. Users have no way to know what works without reading code.
        </description>
      </weakness>

      <weakness>
        <title>No Template Interaction Testing</title>
        <severity>MEDIUM</severity>
        <description>
          Phase 32 (template monomorphization) and Phase 1-6 (C++23 features)
          developed independently. No tests verify they work together. Risk of
          C++ syntax in monomorphized output.
        </description>
      </weakness>
    </weaknesses>
  </quality-assessment>

  <conclusion>
    <summary>
      Phase 1-6 C++23 feature implementations are architecturally sound with strong
      unit test coverage (87.5% pass rate), but suffer from two critical gaps:

      1. **Header file skipping** blocks 70% of integration testing (Phase 33 suite)
      2. **No validation** of features in real-world C++23 code contexts

      Actual C++23 coverage is **10-12%** (Phase 1-3 complete, Phase 4 blocked,
      Phases 5-6 partial), not the 20-25% claimed in documentation. The gap between
      unit test success and integration test failure reveals fundamental architecture
      issues that must be addressed in Phase 7.
    </summary>

    <honest-assessment>
      **What's Working:**
      - Multidimensional subscript operators (Phase 1): ✅ Complete
      - Static operators (Phase 2): ✅ Complete
      - [[assume]] attribute (Phase 3): ✅ Complete (3 strategies)
      - auto(x) decay-copy (Phase 6): ✅ Complete (simple cases)
      - Unit test infrastructure: ✅ Excellent (70/80 passing)

      **What's Not Working:**
      - Deducing this (Phase 4): ❌ API blocked (Clang 17 vs 18)
      - if consteval (Phase 5): ⚠️ Runtime fallback only (loses optimization)
      - Constexpr enhancements (Phase 6): ⚠️ Simple cases only
      - Integration with real C++23 code: ❌ 0% (header skipping)
      - CTAD inherited (original plan): ❌ Not implemented
      - Multi-file transpilation: ❌ Broken by design

      **Critical Blockers:**
      1. Header file skipping (70% of tests blocked)
      2. Clang API version (Phase 4 non-functional)
      3. Zero integration testing (false confidence)
    </honest-assessment>

    <phase-7-priorities>
      <priority rank="1">
        **Fix header file skipping** - Enables 91 tests, validates all Phase 1-6 work
      </priority>
      <priority rank="2">
        **Add integration tests** - Risk mitigation, verify real-world usage
      </priority>
      <priority rank="3">
        **Update user documentation** - Set realistic expectations
      </priority>
      <priority rank="4">
        **Implement CTAD inherited** - Complete original plan, 10 more tests
      </priority>
      <priority rank="5">
        **Improve constexpr evaluation** - High user value, incremental improvement
      </priority>
    </phase-7-priorities>

    <key-metrics>
      <metric>
        <name>Unit Test Pass Rate</name>
        <value>87.5% (70/80)</value>
        <trend>Good - individual features work</trend>
      </metric>
      <metric>
        <name>Integration Test Pass Rate</name>
        <value>0.0% (0/130)</value>
        <trend>Critical - no validation in real code</trend>
      </metric>
      <metric>
        <name>Actual C++23 Coverage</name>
        <value>10-12%</value>
        <note>Lower than claimed 20-25% due to Phase 4 blocker and partial implementations</note>
      </metric>
      <metric>
        <name>Tests Blocked by Header Skipping</name>
        <value>~91/130 (70%)</value>
        <note>Single architectural issue affecting majority of validation</note>
      </metric>
      <metric>
        <name>Phase 7 Estimated Pass Rate</name>
        <value>45-69% (midpoint 57%)</value>
        <note>If header skipping fixed + Phase 4 API available</note>
      </metric>
    </key-metrics>
  </conclusion>
</gaps-analysis>
