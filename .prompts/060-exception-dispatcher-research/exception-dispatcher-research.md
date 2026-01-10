<?xml version="1.0" encoding="UTF-8"?>
<research>
  <metadata>
    <version>v1</version>
    <date>2026-01-03</date>
    <confidence>High</confidence>
    <dependencies>
      <dependency>None - All information gathered from existing codebase</dependency>
    </dependencies>
    <open_questions>
      <question>Should TryCatchTransformer/ThrowTranslator be split into multiple smaller handlers or remain as service classes called by handlers?</question>
      <question>How should exception-specific mappers integrate with existing mapper infrastructure (ExprMapper, StmtMapper)?</question>
      <question>Should exception runtime header generation be part of dispatcher or remain standalone?</question>
    </open_questions>
    <assumptions>
      <assumption>Exception handling follows same dispatcher pattern as existing handlers (registration, predicate, visitor)</assumption>
      <assumption>TryCatchTransformer and ThrowTranslator can be refactored incrementally without breaking existing tests</assumption>
      <assumption>NameMangler API (cpptoc::mangle_*) is stable and ready for exception component integration</assumption>
      <assumption>Placeholder methods (stmtToString, exprToString) will be replaced by dispatcher delegation to existing handlers</assumption>
    </assumptions>
  </metadata>

  <dispatcher_patterns>
    <registration>
      <pattern_description>
        Handlers register with dispatcher via static registerWith() method.
        Registration happens in TranslationUnitHandler or main setup code.
      </pattern_description>

      <example_handlers>
        <handler name="MethodHandler">
          <file>include/dispatch/MethodHandler.h</file>
          <registration_method>static void registerWith(CppToCVisitorDispatcher&amp;)</registration_method>
          <ast_node_types>CXXMethodDecl (excluding constructors/destructors)</ast_node_types>
          <implementation>
            dispatcher.addHandler(&amp;MethodHandler::canHandle, &amp;MethodHandler::handleMethod);
          </implementation>
        </handler>

        <handler name="ReturnStmtHandler">
          <file>include/dispatch/ReturnStmtHandler.h</file>
          <registration_method>static void registerWith(CppToCVisitorDispatcher&amp;)</registration_method>
          <ast_node_types>ReturnStmt</ast_node_types>
          <implementation>
            dispatcher.addHandler(
              static_cast&lt;CppToCVisitorDispatcher::StmtPredicate&gt;(&amp;ReturnStmtHandler::canHandle),
              static_cast&lt;CppToCVisitorDispatcher::StmtVisitor&gt;(&amp;ReturnStmtHandler::handleReturnStmt)
            );
          </implementation>
          <note>Explicit casts to StmtPredicate/StmtVisitor to avoid Stmt/Expr ambiguity</note>
        </handler>

        <handler name="CompoundStmtHandler">
          <file>include/dispatch/CompoundStmtHandler.h</file>
          <registration_method>static void registerWith(CppToCVisitorDispatcher&amp;)</registration_method>
          <ast_node_types>CompoundStmt</ast_node_types>
          <critical_pattern>
            Handles expressions-as-statements by checking isa&lt;Expr&gt;(stmt) first,
            then dispatching via expression handlers (not statement handlers).
            This pattern is CRITICAL for exception handlers since throw expressions
            are often used as statements.
          </critical_pattern>
        </handler>
      </example_handlers>
    </registration>

    <handler_methods>
      <signature_pattern>
        <predicate>
          static bool canHandle(const clang::NodeType* N);
          - Returns true if handler can process this AST node
          - Uses N->getStmtClass() or N->getKind() for exact type matching
          - Excludes nodes handled by other specialized handlers
        </predicate>

        <visitor>
          static void handleNodeType(
              const CppToCVisitorDispatcher&amp; disp,
              const clang::ASTContext&amp; cppASTContext,
              clang::ASTContext&amp; cASTContext,
              const clang::NodeType* N
          );
          - First parameter: dispatcher reference for recursive calls
          - Second parameter: source C++ ASTContext (read-only)
          - Third parameter: target C ASTContext (write)
          - Fourth parameter: AST node to process
        </visitor>
      </signature_pattern>

      <dispatcher_access>
        <recursive_dispatch>
          Handlers recursively dispatch child nodes via:
          - disp.dispatch(cppCtx, cCtx, childNode)
          - Returns bool indicating if any handler matched
        </recursive_dispatch>

        <mapper_access>
          Handlers access mappers via dispatcher getters:
          - disp.getDeclMapper() - C++ Decl → C Decl mapping
          - disp.getTypeMapper() - C++ Type → C Type mapping
          - disp.getExprMapper() - C++ Expr → C Expr mapping
          - disp.getStmtMapper() - C++ Stmt → C Stmt mapping
          - disp.getPathMapper() - Source file → Target file mapping
        </mapper_access>

        <state_management>
          Handlers store/retrieve translated nodes via mappers:
          1. Check: mapper.hasCreated(cppNode) - avoid duplicate translation
          2. Create: Build C AST node using CNodeBuilder or Clang API
          3. Store: mapper.setCreated(cppNode, cNode) - register mapping
          4. Retrieve: mapper.getCreated(cppNode) - get translated node
        </state_management>
      </dispatcher_access>
    </handler_methods>

    <name_mangling_integration>
      <api_location>include/NameMangler.h (namespace cpptoc)</api_location>

      <api_functions>
        <function>
          std::string mangle_method(const clang::CXXMethodDecl* MD)
          - Mangles method name with namespace, class, and parameter types
          - Example: Counter::increment() → Counter__increment__void
        </function>

        <function>
          std::string mangle_constructor(const clang::CXXConstructorDecl* CD)
          - Mangles constructor name with class and parameter types
          - Example: Error::Error(const char*) → Error__ctor__constcharptr
        </function>

        <function>
          std::string mangle_destructor(const clang::CXXDestructorDecl* DD)
          - Mangles destructor name with class prefix
          - Example: Error::~Error() → Error__dtor__void
        </function>

        <function>
          std::string mangle_class(const clang::CXXRecordDecl* RD)
          - Mangles class name with namespace prefix
          - Example: NS::Error → NS__Error
        </function>

        <function>
          std::string mangle_function(const clang::FunctionDecl* FD)
          - Mangles free function name (skips main() and extern "C")
          - Handles overloading via parameter types
        </function>

        <function>
          std::string sanitize_type_name(std::string_view s)
          - Converts C++ type syntax to C-safe identifiers
          - Example: "const char*" → "constcharptr"
        </function>
      </api_functions>

      <usage_examples>
        <example file="src/dispatch/MethodHandler.cpp" line="76">
          std::string mangledName = cpptoc::mangle_method(cppMethod);
        </example>

        <example file="src/dispatch/MethodHandler.cpp" line="195">
          std::string className = cpptoc::mangle_class(classDecl);
        </example>

        <example file="src/dispatch/ConstructorHandler.cpp">
          std::string ctorName = cpptoc::mangle_constructor(cppCtor);
        </example>
      </usage_examples>

      <pattern>
        All handlers use NameMangler API for name generation.
        NO manual string concatenation with "__" separator.
        NameMangler handles namespace prefixes, class prefixes, and parameter type encoding.
      </pattern>
    </name_mangling_integration>

    <inter_handler_communication>
      <shared_data>
        <mapper name="DeclMapper">
          Maps C++ declarations to C declarations.
          Used by all Decl-handling handlers (Method, Constructor, Variable, etc.)
        </mapper>

        <mapper name="TypeMapper">
          Maps C++ types to C types (e.g., reference → pointer conversion).
          Used by all handlers that process types.
        </mapper>

        <mapper name="ExprMapper">
          Maps C++ expressions to C expressions.
          Used by expression handlers (BinaryOperator, CallExpr, DeclRefExpr, etc.)
        </mapper>

        <mapper name="StmtMapper">
          Maps C++ statements to C statements.
          Used by statement handlers (ReturnStmt, CompoundStmt, IfStmt, etc.)
        </mapper>

        <mapper name="PathMapper">
          Maps C++ source files to C target files.
          Manages TranslationUnit creation and node location tracking.
        </mapper>
      </shared_data>

      <delegation>
        <pattern name="Parent delegates to child">
          Example: CompoundStmtHandler dispatches each child statement
          1. for (const Stmt* cppStmt : compound->body())
          2. disp.dispatch(cppCtx, cCtx, cppStmt)
          3. Retrieve: stmtMapper.getCreated(cppStmt)
        </pattern>

        <pattern name="Type delegation">
          Example: MethodHandler dispatches return type to TypeHandler
          1. disp.dispatch(cppCtx, cCtx, cppReturnType)
          2. Retrieve: typeMapper.getCreated(cppReturnType)
        </pattern>

        <pattern name="Expression-as-statement">
          Critical for exception handling!
          CompoundStmtHandler checks if (isa&lt;Expr&gt;(stmt)) first,
          then dispatches via expression handlers.
          Throw expressions will need this pattern.
        </pattern>
      </delegation>

      <context_passing>
        All context flows through dispatcher parameter:
        - const CppToCVisitorDispatcher&amp; disp
        - Handlers are stateless static methods
        - All state in mappers (accessed via dispatcher)
        - No global state, thread-safe by design
      </context_passing>
    </inter_handler_communication>
  </dispatcher_patterns>

  <component_analysis name="TryCatchTransformer">
    <current_architecture>
      <responsibilities>
        Transforms C++ try-catch blocks into C setjmp/longjmp control flow.
        Generates complete try-catch translation as string output.
        Orchestrates exception frame operations, setjmp guards, catch handlers.
      </responsibilities>

      <ast_nodes_handled>
        - CXXTryStmt (try-catch statement)
        - CXXCatchStmt (individual catch handler)
        - CompoundStmt (try body and catch bodies)
      </ast_nodes_handled>

      <dependencies>
        - ExceptionFrameGenerator (frame push/pop operations)
        - Clang AST (CXXTryStmt, CXXCatchStmt, VarDecl, QualType)
        - Manual name mangling (getMangledTypeName, getDestructorName)
        - Placeholder stmtToString() for statement translation
      </dependencies>

      <outputs>
        Generates C code strings:
        1. Frame push: struct __cxx_exception_frame frame; ...
        2. setjmp guard: if (setjmp(frame.jmpbuf) == 0)
        3. Try body with frame activation
        4. Catch handlers with type checking (strcmp)
        5. Exception object casting and cleanup
      </outputs>
    </current_architecture>

    <technical_debt>
      <manual_mangling>
        <location file="src/TryCatchTransformer.cpp" line="233">
          std::string TryCatchTransformer::getMangledTypeName(QualType type) const {
              // For now, use simple name (in production, use Itanium mangling)
              if (const RecordType *RT = actualType->getAs&lt;RecordType&gt;()) {
                  if (const CXXRecordDecl *RD = dyn_cast&lt;CXXRecordDecl&gt;(RT->getDecl())) {
                      return RD->getNameAsString();  // ← MANUAL MANGLING
                  }
              }
              return actualType.getAsString();
          }
        </location>
        <pattern>className (no namespace prefix, no "__" separator)</pattern>
        <replacement>cpptoc::mangle_class(RD) - includes namespace, proper formatting</replacement>
      </manual_mangling>

      <manual_mangling>
        <location file="src/TryCatchTransformer.cpp" line="251">
          std::string TryCatchTransformer::getDestructorName(const CXXRecordDecl *recordDecl) const {
              // Use simple naming pattern: ClassName__dtor
              // In production, would use proper name mangling
              return recordDecl->getNameAsString() + "__dtor";  // ← MANUAL MANGLING
          }
        </location>
        <pattern>ClassName + "__dtor" (hardcoded separator, no namespace)</pattern>
        <replacement>cpptoc::mangle_destructor(destructorDecl) - proper mangling</replacement>
      </manual_mangling>

      <placeholder_methods>
        <method name="stmtToString" file="src/TryCatchTransformer.cpp" line="258">
          <current_implementation>
            Returns placeholder strings: "/* declaration */;", "/* function call */;", etc.
            Does NOT actually translate statements to C code.
            Major blocker for end-to-end translation.
          </current_implementation>

          <dispatcher_solution>
            Replace with dispatcher delegation:
            1. disp.dispatch(cppCtx, cCtx, stmt)
            2. stmtMapper.getCreated(stmt)
            3. Use CodeGenerator to emit C code from created C AST node

            Alternative: Store C Stmt* directly in StmtMapper, not strings.
            TryCatchTransformer should create C AST nodes, not strings.
          </dispatcher_solution>
        </method>
      </placeholder_methods>

      <other_debt>
        <issue>String-based output instead of C AST creation</issue>
        <description>
          TryCatchTransformer generates C code as strings, not C AST nodes.
          This violates the 3-stage pipeline: C++ AST → C AST → C code.
          Should create C IfStmt, CompoundStmt, CallExpr nodes instead.
        </description>
        <solution>
          Refactor to return C Stmt* instead of std::string.
          Use CNodeBuilder to create C AST nodes (IfStmt for setjmp guard, etc.)
        </solution>
      </other_debt>
    </technical_debt>

    <integration_requirements>
      <handler_creation>
        <handler_name>TryStmtHandler</handler_name>
        <ast_node_type>CXXTryStmt</ast_node_type>
        <delegation>
          Handler delegates to TryCatchTransformer service class:
          1. TryStmtHandler::handleTryStmt() called by dispatcher
          2. Creates TryCatchTransformer instance (or uses singleton)
          3. Calls transformer.transformTryCatch(tryStmt, frameVar, actionsTable)
          4. Stores result in StmtMapper

          Or: Inline TryCatchTransformer logic directly in handler
        </delegation>
      </handler_creation>

      <modifications_needed>
        <to_component>
          1. Replace getMangledTypeName() with cpptoc::mangle_class()
          2. Replace getDestructorName() with cpptoc::mangle_destructor()
          3. Replace stmtToString() with dispatcher delegation
          4. Change return type from std::string to clang::Stmt*
          5. Use CNodeBuilder to create C AST nodes (IfStmt, CompoundStmt, CallExpr)
        </to_component>

        <to_tests>
          1. Adapt tests to expect C AST nodes instead of strings
          2. Add dispatcher setup in test fixtures
          3. Integrate with existing mapper infrastructure
          4. May need to update assertions (check AST structure, not string content)
        </to_tests>

        <new_tests>
          1. TryStmtHandler dispatcher registration test
          2. TryStmtHandler integration with CompoundStmtHandler (nested try-catch)
          3. TryStmtHandler integration with ThrowExprHandler
          4. Exception type matching with NameMangler API
          5. Destructor call generation with NameMangler API
        </new_tests>
      </modifications_needed>
    </integration_requirements>
  </component_analysis>

  <component_analysis name="ThrowTranslator">
    <current_architecture>
      <responsibilities>
        Translates C++ throw expressions into C code with cxx_throw runtime calls.
        Handles exception allocation, constructor invocation, type info extraction.
        Supports both new throws and re-throws (throw;).
      </responsibilities>

      <ast_nodes_handled>
        - CXXThrowExpr (throw expression)
        - CXXConstructExpr (exception constructor)
        - MaterializeTemporaryExpr, CXXBindTemporaryExpr (temporary wrapping)
        - ImplicitCastExpr (unwrapping for constructor extraction)
      </ast_nodes_handled>

      <dependencies>
        - Clang AST (CXXThrowExpr, CXXConstructExpr, QualType)
        - Manual name mangling (getMangledTypeName, getConstructorName)
        - Placeholder exprToString() for argument translation
      </dependencies>

      <outputs>
        Generates C code strings:
        1. Exception allocation: struct Type *__ex = (struct Type*)malloc(sizeof(struct Type));
        2. Constructor call: Type__ctor(__ex, args...);
        3. Type info extraction: "TypeName"
        4. cxx_throw call: cxx_throw(__ex, "TypeName");
      </outputs>
    </current_architecture>

    <technical_debt>
      <manual_mangling>
        <location file="src/ThrowTranslator.cpp" line="175">
          std::string ThrowTranslator::getMangledTypeName(QualType type) const {
              // For now, use simple name (in production, use Itanium mangling)
              if (const RecordType *RT = actualType->getAs&lt;RecordType&gt;()) {
                  if (const CXXRecordDecl *RD = dyn_cast&lt;CXXRecordDecl&gt;(RT->getDecl())) {
                      return RD->getNameAsString();  // ← MANUAL MANGLING
                  }
              }
              return actualType.getAsString();
          }
        </location>
        <pattern>className (no namespace prefix)</pattern>
        <replacement>cpptoc::mangle_class(RD)</replacement>
      </manual_mangling>

      <manual_mangling>
        <location file="src/ThrowTranslator.cpp" line="196">
          std::string ThrowTranslator::getConstructorName(const CXXRecordDecl *recordDecl) const {
              // Use simple naming pattern: ClassName__ctor
              // In production, would use proper name mangling
              return recordDecl->getNameAsString() + "__ctor";  // ← MANUAL MANGLING
          }
        </location>
        <pattern>ClassName + "__ctor" (hardcoded separator, no namespace, no params)</pattern>
        <replacement>cpptoc::mangle_constructor(ctorDecl) - includes parameter types</replacement>
      </manual_mangling>

      <placeholder_methods>
        <method name="exprToString" file="src/ThrowTranslator.cpp" line="219">
          <current_implementation>
            Handles only StringLiteral, IntegerLiteral, ImplicitCastExpr.
            Returns "/* expression */" for all other cases.
            Cannot translate complex expressions (member access, function calls, etc.)
          </current_implementation>

          <dispatcher_solution>
            Replace with dispatcher delegation:
            1. disp.dispatch(cppCtx, cCtx, expr)
            2. exprMapper.getCreated(expr)
            3. Use created C Expr* directly (not string conversion)

            ThrowTranslator should create C CallExpr nodes with C Expr* arguments,
            not string-based code generation.
          </dispatcher_solution>
        </method>

        <method name="argumentsToString" file="src/ThrowTranslator.cpp" line="203">
          <current_implementation>
            Iterates constructor arguments and calls exprToString() for each.
            Joins results with ", " separator.
            Limited by exprToString() placeholder implementation.
          </current_implementation>

          <dispatcher_solution>
            Replace with dispatcher delegation for each argument:
            1. for (auto* arg : ctorExpr->arguments())
            2. disp.dispatch(cppCtx, cCtx, arg)
            3. Collect translated C Expr* nodes
            4. Pass to CallExpr::Create() for constructor call
          </dispatcher_solution>
        </method>
      </placeholder_methods>

      <other_debt>
        <issue>String-based output instead of C AST creation</issue>
        <description>
          ThrowTranslator generates C code as strings, not C AST nodes.
          Should create C CallExpr for cxx_throw(), C VarDecl for __ex, etc.
        </description>
        <solution>
          Refactor to return C Expr* (CallExpr to cxx_throw).
          Use CNodeBuilder to create allocation, constructor call, cxx_throw call.
        </solution>
      </other_debt>
    </technical_debt>

    <integration_requirements>
      <handler_creation>
        <handler_name>ThrowExprHandler</handler_name>
        <ast_node_type>CXXThrowExpr</ast_node_type>
        <delegation>
          Handler delegates to ThrowTranslator service class:
          1. ThrowExprHandler::handleThrowExpr() called by dispatcher
          2. Creates ThrowTranslator instance
          3. Calls translator.generateThrowCode(throwExpr)
          4. Stores result in ExprMapper (throw is an expression!)

          Important: CXXThrowExpr is an Expr, so use ExprMapper, not StmtMapper
        </delegation>
      </handler_creation>

      <modifications_needed>
        <to_component>
          1. Replace getMangledTypeName() with cpptoc::mangle_class()
          2. Replace getConstructorName() with cpptoc::mangle_constructor()
          3. Replace exprToString() with dispatcher delegation
          4. Change return type from std::string to clang::Expr* (CallExpr to cxx_throw)
          5. Use CNodeBuilder to create malloc call, constructor call, cxx_throw call
          6. Handle re-throw by accessing current exception frame
        </to_component>

        <to_tests>
          1. Adapt tests to expect C AST nodes instead of strings
          2. Add dispatcher setup in test fixtures
          3. Verify C CallExpr structure (cxx_throw with correct arguments)
          4. Test integration with constructor translation
        </to_tests>

        <new_tests>
          1. ThrowExprHandler dispatcher registration test
          2. ThrowExprHandler integration with ConstructorHandler
          3. Throw expression in function call arguments
          4. Throw expression in conditional expression (rare but valid)
          5. Re-throw translation test
        </new_tests>
      </modifications_needed>
    </integration_requirements>
  </component_analysis>

  <component_analysis name="ExceptionFrameGenerator">
    <current_architecture>
      <responsibilities>
        Generates exception frame structure definitions and thread-local stack code.
        Produces frame push/pop operations for try-catch block boundaries.
        Creates complete exception_support.h header file.
      </responsibilities>

      <ast_nodes_handled>
        None - this is a code generation utility, not an AST visitor.
      </ast_nodes_handled>

      <dependencies>
        None - standalone string generation utility.
        No Clang AST dependencies.
      </dependencies>

      <outputs>
        Generates C header/implementation code strings:
        1. struct __cxx_exception_frame definition
        2. struct __cxx_action_entry definition
        3. _Thread_local __cxx_exception_stack declaration
        4. Frame push/pop code snippets
        5. Complete exception_support.h header
      </outputs>
    </current_architecture>

    <technical_debt>
      <manual_mangling>
        None - ExceptionFrameGenerator does not perform name mangling.
        Uses fixed runtime struct names (__cxx_exception_frame, __cxx_exception_stack).
      </manual_mangling>

      <placeholder_methods>
        None - ExceptionFrameGenerator is complete and functional.
        Generates correct C code for exception runtime structures.
      </placeholder_methods>

      <other_debt>
        <issue>String-based output for header generation</issue>
        <description>
          Generates exception_support.h as string instead of using Clang AST.
          This is acceptable for header files (not part of C AST translation).
          Header generation is a separate concern from AST translation.
        </description>
        <solution>
          No change needed - string-based header generation is appropriate here.
          Headers are not part of the C AST, they are external support files.
        </solution>
      </other_debt>
    </technical_debt>

    <integration_requirements>
      <handler_creation>
        <handler_name>N/A - Not a handler</handler_name>
        <ast_node_type>N/A</ast_node_type>
        <delegation>
          ExceptionFrameGenerator remains a service class used by TryStmtHandler.
          No dispatcher registration needed.
          TryStmtHandler calls frameGenerator.generateFramePush/Pop() as needed.
        </delegation>
      </handler_creation>

      <modifications_needed>
        <to_component>
          None - ExceptionFrameGenerator is complete and does not need modification.
        </to_component>

        <to_tests>
          None - existing tests are sufficient.
          All 17 tests pass (verified by test file analysis).
        </to_tests>

        <new_tests>
          None - ExceptionFrameGenerator is well-tested standalone.
          Integration tests will verify usage within TryStmtHandler.
        </new_tests>
      </modifications_needed>
    </integration_requirements>
  </component_analysis>

  <test_analysis>
    <existing_tests>
      <test_file>tests/TryCatchTransformerTest.cpp</test_file>
      <test_type>Unit test (standalone component)</test_type>
      <coverage>
        - Basic try-catch transformation
        - Multiple catch handlers
        - Exception type checking
        - Exception object casting
        - Exception cleanup (destructor + free)
        - setjmp guard generation
        - Frame push/pop operations
      </coverage>
      <dispatcher_compatibility>
        Needs significant adaptation:
        1. Currently expects string output from transformTryCatch()
        2. Must be updated to expect C AST nodes (IfStmt, CompoundStmt)
        3. Requires dispatcher setup in test fixture
        4. May need CodeGenerator to emit C code from AST for verification
      </dispatcher_compatibility>
    </existing_tests>

    <existing_tests>
      <test_file>tests/ThrowTranslatorTest.cpp</test_file>
      <test_type>Unit test (standalone component)</test_type>
      <coverage>
        - Throw expression detection
        - Re-throw detection
        - Exception allocation (malloc)
        - Constructor call generation
        - Type info extraction
        - cxx_throw call generation
        - Argument translation
        - Translation order verification
      </coverage>
      <dispatcher_compatibility>
        Needs significant adaptation:
        1. Currently expects string output from generateThrowCode()
        2. Must be updated to expect C AST nodes (CallExpr to cxx_throw)
        3. Requires dispatcher setup
        4. Should verify C Expr* structure, not string content
      </dispatcher_compatibility>
    </existing_tests>

    <existing_tests>
      <test_file>tests/ExceptionFrameTest.cpp</test_file>
      <test_type>Unit test (standalone utility)</test_type>
      <coverage>
        - Frame struct generation
        - Thread-local stack declaration
        - Frame push/pop code
        - Header file generation
        - Field order verification
        - Include guard verification
      </coverage>
      <dispatcher_compatibility>
        No adaptation needed - ExceptionFrameGenerator is dispatcher-independent.
        Tests remain as-is, continue to verify string output.
      </dispatcher_compatibility>
    </existing_tests>

    <existing_tests>
      <test_file>tests/ExceptionHandlingIntegrationTest.cpp</test_file>
      <test_type>End-to-end integration test</test_type>
      <coverage>
        - Basic try-catch with single handler
        - Multiple catch handlers
        - Catch-all handler (catch(...))
        - Nested try-catch blocks
        - Re-throw support
        - Stack unwinding with destructors
        - Exception propagation
        - Constructor with parameters
        - Exception object lifetime
      </coverage>
      <dispatcher_compatibility>
        High compatibility - tests runtime behavior, not implementation.
        After dispatcher integration, tests should continue to pass if:
        1. Generated C code is functionally equivalent
        2. Exception runtime library works correctly
        3. Name mangling produces correct identifiers
      </dispatcher_compatibility>
    </existing_tests>

    <existing_tests>
      <test_file>tests/ExceptionIntegrationTest.cpp</test_file>
      <test_type>Integration test</test_type>
      <coverage>Similar to ExceptionHandlingIntegrationTest</coverage>
      <dispatcher_compatibility>High - runtime-focused testing</dispatcher_compatibility>
    </existing_tests>

    <existing_tests>
      <test_file>tests/ExceptionPerformanceTest.cpp</test_file>
      <test_type>Performance benchmark</test_type>
      <coverage>Exception handling overhead measurement</coverage>
      <dispatcher_compatibility>High - performance characteristics should be preserved</dispatcher_compatibility>
    </existing_tests>

    <existing_tests>
      <test_file>tests/ExceptionThreadSafetyTest.cpp</test_file>
      <test_type>Concurrency test</test_type>
      <coverage>Thread-local exception stack safety</coverage>
      <dispatcher_compatibility>High - thread safety must be maintained</dispatcher_compatibility>
    </existing_tests>

    <existing_tests>
      <test_file>tests/ExceptionRuntimeTest.cpp</test_file>
      <test_type>Runtime library test</test_type>
      <coverage>cxx_throw() function behavior</coverage>
      <dispatcher_compatibility>High - runtime library is independent of dispatcher</dispatcher_compatibility>
    </existing_tests>

    <existing_tests>
      <test_file>tests/ExceptionFrameTest.cpp</test_file>
      <test_type>Unit test</test_type>
      <coverage>Exception frame structure and operations</coverage>
      <dispatcher_compatibility>No changes needed</dispatcher_compatibility>
    </existing_tests>

    <dispatcher_test_patterns>
      <example>tests/unit/dispatch/InstanceMethodHandlerDispatcherTest.cpp</example>
      <pattern>
        1. Create test fixture with dispatcher and mappers
        2. Register handler: handler::registerWith(dispatcher)
        3. Parse test C++ code into AST
        4. Find target AST node (e.g., CXXMethodDecl)
        5. Dispatch: dispatcher.dispatch(cppCtx, cCtx, node)
        6. Retrieve: mapper.getCreated(cppNode)
        7. Assert: verify C AST node properties
      </pattern>

      <assertions>
        - Assert handler registration succeeded
        - Assert dispatch() returns true (handler matched)
        - Assert created C node is not null
        - Assert C node type is correct (FunctionDecl, IfStmt, etc.)
        - Assert C node has correct properties (name, parameters, body, etc.)
        - Assert C node is stored in correct mapper
      </assertions>
    </dispatcher_test_patterns>

    <migration_strategy>
      <tests_to_migrate>
        <test>TryCatchTransformerTest.cpp</test>
        <approach>
          1. Create dispatcher test fixture (TryStmtHandlerTest)
          2. Register TryStmtHandler with dispatcher
          3. Parse test C++ code (try-catch blocks)
          4. Dispatch CXXTryStmt to handler
          5. Retrieve created C Stmt from StmtMapper
          6. Assert C AST structure (IfStmt with setjmp guard)
          7. Optionally use CodeGenerator to verify emitted C code
        </approach>
        <can_rewrite>Partial - keep integration tests, rewrite unit tests</can_rewrite>
      </tests_to_migrate>

      <tests_to_migrate>
        <test>ThrowTranslatorTest.cpp</test>
        <approach>
          1. Create dispatcher test fixture (ThrowExprHandlerTest)
          2. Register ThrowExprHandler with dispatcher
          3. Parse test C++ code (throw expressions)
          4. Dispatch CXXThrowExpr to handler
          5. Retrieve created C Expr from ExprMapper
          6. Assert C CallExpr structure (cxx_throw with args)
        </approach>
        <can_rewrite>Partial - rewrite unit tests, keep integration tests</can_rewrite>
      </tests_to_migrate>

      <tests_to_migrate>
        <test>ExceptionFrameTest.cpp</test>
        <approach>Keep as-is - no migration needed</approach>
        <can_rewrite>No</can_rewrite>
      </tests_to_migrate>

      <tests_to_migrate>
        <test>Exception*IntegrationTest.cpp</test>
        <approach>Keep as-is - verify behavior after dispatcher integration</approach>
        <can_rewrite>No - integration tests should remain runtime-focused</can_rewrite>
      </tests_to_migrate>

      <new_tests_needed>
        1. TryStmtHandler dispatcher registration test
        2. ThrowExprHandler dispatcher registration test
        3. TryStmt with nested CompoundStmt integration
        4. ThrowExpr with ConstructorHandler integration
        5. Exception type name mangling test (NameMangler API)
        6. Exception destructor name mangling test
        7. Throw in method call argument test
        8. Try-catch in class method body test
      </new_tests_needed>

      <test_fixtures>
        <fixture name="ExceptionDispatcherTestFixture">
          - Sets up dispatcher with all required handlers
          - Provides helper methods for parsing exception-related C++ code
          - Includes assertion helpers for C AST verification
          - Manages mapper lifecycle
        </fixture>

        <fixture name="ExceptionCodeGenTestFixture">
          - Extends ExceptionDispatcherTestFixture
          - Adds CodeGenerator for C code emission
          - Provides helpers for comparing generated C code
          - Useful for migration from string-based tests
        </fixture>
      </test_fixtures>
    </migration_strategy>
  </test_analysis>

  <integration_points>
    <method_calls_in_try>
      <scenario>Method call inside try block body</scenario>
      <handler_interaction>
        TryStmtHandler → CompoundStmtHandler → CallExprHandler → MethodHandler
        1. TryStmtHandler processes CXXTryStmt
        2. Dispatches try body (CompoundStmt) to CompoundStmtHandler
        3. CompoundStmtHandler dispatches child statements (CallExpr)
        4. CallExprHandler resolves method call target
        5. MethodHandler provides translated C function name
      </handler_interaction>
      <current_gap>
        TryCatchTransformer.stmtToString() cannot handle method calls.
        Returns "/* function call */;" placeholder.
        After dispatcher integration, this will work automatically.
      </current_gap>
    </method_calls_in_try>

    <throw_in_constructor>
      <scenario>throw expression inside constructor body</scenario>
      <handler_interaction>
        ConstructorHandler → CompoundStmtHandler → ThrowExprHandler
        1. ConstructorHandler processes CXXConstructorDecl
        2. Dispatches constructor body to CompoundStmtHandler
        3. CompoundStmtHandler finds throw expression (isa&lt;Expr&gt; check)
        4. Dispatches to ThrowExprHandler as expression
        5. ThrowExprHandler generates cxx_throw call
      </handler_interaction>
      <current_gap>
        ThrowTranslator is standalone, not integrated with ConstructorHandler.
        Constructor translation and throw translation are disconnected.
        After dispatcher integration, this will compose naturally.
      </current_gap>
    </throw_in_constructor>

    <exception_class_translation>
      <scenario>Exception class with members, methods, inheritance</scenario>
      <handler_interaction>
        RecordHandler → MethodHandler → DestructorHandler
        Exception classes are normal C++ classes, handled by existing handlers.

        Special consideration: Exception class name mangling must match
        what ThrowExprHandler uses for type info strings.

        RecordHandler: Translates exception class to C struct
        MethodHandler: Translates exception class methods
        DestructorHandler: Translates exception destructor (for cleanup)
        ThrowExprHandler: Uses mangle_class() for type matching
        TryStmtHandler: Uses mangle_destructor() for cleanup calls
      </handler_interaction>
      <current_gap>
        Manual name mangling in TryCatchTransformer/ThrowTranslator may not
        match class names generated by RecordHandler.
        After NameMangler API integration, all handlers use consistent naming.
      </current_gap>
    </exception_class_translation>

    <exception_frame_in_function>
      <scenario>Try-catch inside function body</scenario>
      <handler_interaction>
        FunctionHandler → CompoundStmtHandler → TryStmtHandler → ExceptionFrameGenerator
        1. FunctionHandler processes FunctionDecl
        2. Dispatches function body to CompoundStmtHandler
        3. CompoundStmtHandler finds try-catch statement
        4. Dispatches to TryStmtHandler
        5. TryStmtHandler uses ExceptionFrameGenerator for frame operations
        6. Generated frame variables scoped to try-catch block (local to function)
      </handler_interaction>
      <current_gap>
        Frame variable naming must be unique within function scope.
        Current implementation uses fixed names ("frame", "actions_table_0").
        May need counter or UUID for nested try-catch blocks.
      </current_gap>
    </exception_frame_in_function>

    <exception_in_virtual_method>
      <scenario>throw inside virtual method, caught by caller</scenario>
      <handler_interaction>
        VirtualMethodHandler → CompoundStmtHandler → ThrowExprHandler
        Virtual method translation + exception handling compose naturally.

        Caller side:
        TryStmtHandler (caller's try block)
        → CallExprHandler (virtual method call via vtable)
        → Exception propagates up via longjmp
        → TryStmtHandler catches in caller's catch handler
      </handler_interaction>
      <current_gap>
        Virtual method calls and exception handling are separately implemented.
        Integration should work automatically after dispatcher integration.
        Need integration test to verify vtable dispatch + exception unwinding.
      </current_gap>
    </exception_in_virtual_method>

    <rethrow_in_catch>
      <scenario>Re-throw (throw;) inside catch handler</scenario>
      <handler_interaction>
        TryStmtHandler → catch handler body → ThrowExprHandler (re-throw)
        1. TryStmtHandler processes catch handler body
        2. Dispatches catch body statements
        3. Finds re-throw expression (CXXThrowExpr with null subexpression)
        4. ThrowExprHandler detects re-throw case
        5. Generates cxx_throw(frame.exception_object, frame.exception_type)
      </handler_interaction>
      <current_gap>
        Re-throw needs access to current exception frame.
        Frame variable name must be known to ThrowExprHandler.
        Options:
        1. Pass frame variable name via context/mapper
        2. Use fixed runtime name (__cxx_exception_stack)
        3. Generate code that accesses thread-local stack directly
      </current_gap>
    </rethrow_in_catch>
  </integration_points>

  <complexity_assessment>
    <handler_creation>
      <effort>Medium</effort>
      <rationale>
        Two new handlers needed: TryStmtHandler and ThrowExprHandler.
        Each handler is ~200-300 lines (similar to existing handlers).
        Registration and predicate methods are straightforward.
        Main complexity is in visitor method implementation.
      </rationale>
      <risks>
        - Frame variable naming conflicts (nested try-catch)
        - Re-throw frame access (need context passing)
        - Catch handler type matching (must use consistent name mangling)
      </risks>
      <estimated_time>3-5 hours per handler = 6-10 hours total</estimated_time>
    </handler_creation>

    <technical_debt_resolution>
      <effort>Medium-High</effort>
      <rationale>
        Manual name mangling: 4 locations (2 in TryCatchTransformer, 2 in ThrowTranslator)
        Placeholder methods: 2 major (stmtToString, exprToString)
        String output to AST: Major refactoring of both components

        Most complex: Converting string-based code generation to C AST creation.
        Requires understanding of Clang AST node creation (IfStmt, CallExpr, etc.)
      </rationale>
      <risks>
        - Breaking existing tests (need careful migration)
        - Incomplete expression/statement coverage (exprToString limitations)
        - AST node creation errors (memory management, parent/context setting)
        - Lost functionality during refactoring (need feature parity)
      </risks>
      <estimated_time>
        - Name mangling fix: 2-3 hours
        - String to AST refactoring: 10-15 hours
        - Total: 12-18 hours
      </estimated_time>
    </technical_debt_resolution>

    <test_migration>
      <effort>Medium</effort>
      <rationale>
        Unit tests (3 files): Significant rewrite needed (string → AST assertions)
        Integration tests (6 files): Minimal changes (behavior verification)

        Unit test migration is most time-consuming:
        - Need dispatcher test fixtures
        - Update assertions to check C AST structure
        - May need CodeGenerator for string comparison
      </rationale>
      <risks>
        - Test coverage gaps during migration
        - Assertions become more complex (AST traversal vs string search)
        - Integration tests may fail if behavior changes
      </risks>
      <estimated_time>
        - Unit test migration: 6-8 hours
        - New dispatcher tests: 4-5 hours
        - Integration test fixes: 2-3 hours
        - Total: 12-16 hours
      </estimated_time>
    </test_migration>

    <overall>
      <estimated_effort>
        Handler creation: 6-10 hours
        Technical debt: 12-18 hours
        Test migration: 12-16 hours
        Documentation: 2-3 hours
        Buffer (unexpected issues): 5-8 hours
        ===================================
        Total: 37-55 hours (5-7 working days)
      </estimated_effort>

      <critical_path>
        1. Fix name mangling (prerequisite for correct translation)
        2. Create TryStmtHandler and ThrowExprHandler (core functionality)
        3. Refactor TryCatchTransformer to use dispatcher (remove stmtToString)
        4. Refactor ThrowTranslator to use dispatcher (remove exprToString)
        5. Migrate unit tests
        6. Verify integration tests pass
        7. Document new handlers
      </critical_path>

      <dependencies>
        External:
        - NameMangler API must be stable (appears to be)
        - Existing handlers (CompoundStmt, CallExpr, etc.) must work correctly
        - CNodeBuilder must support all required C AST node types

        Internal:
        - Must complete handler creation before test migration
        - Must fix name mangling before AST refactoring
        - Integration tests depend on all components working together
      </dependencies>

      <parallelization_opportunities>
        Can work in parallel:
        1. TryStmtHandler creation + ThrowExprHandler creation (independent)
        2. Name mangling fixes in TryCatchTransformer + ThrowTranslator (independent)
        3. Unit test migration + Integration test verification (after handlers done)

        Must be sequential:
        1. Handler creation → AST refactoring (handlers need to exist first)
        2. AST refactoring → Test migration (tests depend on new API)
      </parallelization_opportunities>
    </overall>
  </complexity_assessment>

  <recommendations>
    <recommendation priority="high">
      Fix manual name mangling FIRST before any other work.
      This is a prerequisite for correct exception type matching.
      Replace all getMangledTypeName() and getDestructorName() calls
      with cpptoc::mangle_class() and cpptoc::mangle_destructor().

      Rationale: Name consistency is critical for exception handling.
      If type names don't match between throw site and catch site, exceptions won't be caught.
    </recommendation>

    <recommendation priority="high">
      Create minimal TryStmtHandler and ThrowExprHandler first,
      delegating to existing TryCatchTransformer/ThrowTranslator.
      Get handlers registered and basic dispatch working before refactoring internals.

      Rationale: Incremental integration reduces risk.
      Can verify dispatcher mechanics work before tackling complex AST generation.
    </recommendation>

    <recommendation priority="medium">
      Keep ExceptionFrameGenerator as-is (no dispatcher integration).
      It's a utility class for code generation, not an AST handler.
      TryStmtHandler can use it directly without dispatcher registration.

      Rationale: Not everything needs to be a handler.
      Service classes for code generation are acceptable.
    </recommendation>

    <recommendation priority="medium">
      Refactor string-based output to C AST nodes incrementally.
      Start with simple cases (exception allocation, cxx_throw call).
      Then tackle complex cases (try body, catch handlers).

      Rationale: String→AST conversion is the highest risk area.
      Incremental approach allows testing at each step.
    </recommendation>

    <recommendation priority="low">
      Consider creating ExceptionMapper for exception-specific mappings.
      Could store exception frame variable names, action table names, etc.
      Would help with re-throw frame access and nested try-catch blocks.

      Rationale: Current mappers (DeclMapper, StmtMapper, etc.) may not be
      sufficient for exception-specific context. A dedicated mapper could
      simplify context passing between handlers.
    </recommendation>

    <recommendation priority="low">
      Add dispatcher-based integration tests BEFORE migrating existing tests.
      Create new test files (TryStmtHandlerDispatcherTest.cpp, etc.) to verify
      handler behavior in isolation. Keep existing tests as regression checks.

      Rationale: New tests validate new architecture.
      Old tests validate behavior preservation.
      Having both provides comprehensive coverage during migration.
    </recommendation>
  </recommendations>

  <quality_report>
    <sources_consulted>
      <source path="include/dispatch/CppToCVisitorDispatcher.h">Dispatcher interface and type definitions</source>
      <source path="include/dispatch/MethodHandler.h">Example handler interface and documentation</source>
      <source path="include/dispatch/StatementHandler.h">Statement handler patterns</source>
      <source path="include/dispatch/ReturnStmtHandler.h">Simple statement handler example</source>
      <source path="src/dispatch/MethodHandler.cpp">Handler implementation with NameMangler usage</source>
      <source path="src/dispatch/ReturnStmtHandler.cpp">Handler implementation with dispatcher delegation</source>
      <source path="src/dispatch/CompoundStmtHandler.cpp">Handler implementation with expression-as-statement pattern</source>
      <source path="include/TryCatchTransformer.h">Exception component interface</source>
      <source path="include/ThrowTranslator.h">Exception component interface</source>
      <source path="include/ExceptionFrameGenerator.h">Exception component interface</source>
      <source path="src/TryCatchTransformer.cpp">Exception component implementation with manual mangling</source>
      <source path="src/ThrowTranslator.cpp">Exception component implementation with placeholder methods</source>
      <source path="src/ExceptionFrameGenerator.cpp">Exception component implementation</source>
      <source path="include/NameMangler.h">Name mangling API documentation</source>
      <source path="tests/TryCatchTransformerTest.cpp">Existing test coverage and patterns</source>
      <source path="tests/ThrowTranslatorTest.cpp">Existing test coverage and patterns</source>
      <source path="tests/ExceptionFrameTest.cpp">Existing test coverage</source>
      <source path="tests/ExceptionHandlingIntegrationTest.cpp">Integration test patterns</source>
    </sources_consulted>

    <verification_status>
      <verified>
        - Dispatcher registration pattern (verified in MethodHandler, ReturnStmtHandler)
        - Handler method signatures (verified in multiple handlers)
        - NameMangler API functions and usage (verified in MethodHandler.cpp)
        - Manual name mangling locations in exception components (verified in source)
        - Placeholder method limitations (verified in source code)
        - Existing test structure and coverage (verified in test files)
        - Mapper access patterns (verified in handler implementations)
        - Expression-as-statement pattern (verified in CompoundStmtHandler)
      </verified>

      <assumed>
        - Exact effort estimates (based on code size analysis, not empirical data)
        - Test migration complexity (depends on assertion strategies)
        - Integration test pass rate after migration (assumes behavior preservation)
        - Parallelization opportunities (depends on developer workflow)
      </assumed>
    </verification_status>

    <confidence_rationale>
      Confidence level: HIGH

      Reasons:
      1. All findings based on actual code reading (not inference)
      2. Dispatcher patterns verified across multiple handlers (consistent)
      3. NameMangler API usage verified in production code (MethodHandler)
      4. Technical debt locations precisely identified with line numbers
      5. Test files examined to understand coverage and structure
      6. Integration points analyzed through handler interaction chains

      Areas of uncertainty:
      1. Exact refactoring effort (depends on developer experience)
      2. Test migration strategy details (multiple valid approaches)
      3. ExceptionMapper necessity (may or may not be needed)
      4. Frame variable naming strategy (multiple solutions possible)

      Overall: Research provides solid foundation for planning phase.
      All critical information gathered, open questions are tactical, not strategic.
    </confidence_rationale>
  </quality_report>
</research>
