cmake_minimum_required(VERSION 3.20)
project(cpptoc C CXX)

# Set C++17 standard (SOLID principle: explicit requirements)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# ============================================================================
# Code Coverage Configuration
# ============================================================================
option(ENABLE_COVERAGE "Enable code coverage reporting" OFF)

if(ENABLE_COVERAGE)
    message(STATUS "Code coverage enabled")

    # Add coverage compiler flags
    set(COVERAGE_FLAGS "--coverage -fprofile-arcs -ftest-coverage")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${COVERAGE_FLAGS}")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${COVERAGE_FLAGS}")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} --coverage")

    # Find required tools
    find_program(LCOV_PATH lcov)
    find_program(GENHTML_PATH genhtml)

    if(NOT LCOV_PATH)
        message(WARNING "lcov not found! Coverage reports cannot be generated. Install with: brew install lcov")
    endif()

    if(NOT GENHTML_PATH)
        message(WARNING "genhtml not found! HTML coverage reports cannot be generated.")
    endif()

    # Add custom target for coverage report generation
    if(LCOV_PATH AND GENHTML_PATH)
        add_custom_target(coverage
            COMMAND ${CMAKE_COMMAND} -E echo "Generating coverage report..."

            # Initialize coverage data
            COMMAND ${LCOV_PATH} --directory . --zerocounters

            # Run tests (this will be filled in by the script)
            COMMAND ${CMAKE_COMMAND} -E echo "Run tests before generating coverage"

            # Capture coverage data
            COMMAND ${LCOV_PATH} --directory . --capture --output-file coverage.info

            # Remove system headers and test files from coverage
            COMMAND ${LCOV_PATH} --remove coverage.info '/usr/*' '*/tests/*' '*/build/*' --output-file coverage.info.cleaned

            # Generate HTML report
            COMMAND ${GENHTML_PATH} coverage.info.cleaned --output-directory coverage --demangle-cpp

            COMMAND ${CMAKE_COMMAND} -E echo "Coverage report generated in coverage/"

            WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
            COMMENT "Generating code coverage report"
        )
    endif()
endif()

# Find LLVM and Clang packages
# Using CONFIG mode for better reliability
find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

# Create executable target
# Single responsibility: build the cpptoc tool
add_executable(cpptoc
    src/main.cpp
    src/CppToCFrontendAction.cpp
    src/CppToCConsumer.cpp
    src/CppToCVisitor.cpp
    src/CFGAnalyzer.cpp
    src/NameMangler.cpp
    src/CodeGenerator.cpp
    src/HeaderSeparator.cpp
    src/IncludeGuardGenerator.cpp
    src/DependencyAnalyzer.cpp
    src/FileOutputManager.cpp
    src/CFGAnalyzer.cpp
    src/VirtualMethodAnalyzer.cpp
    src/VptrInjector.cpp
    src/VirtualInheritanceAnalyzer.cpp
)

# Apply LLVM/Clang compile definitions to target
target_compile_definitions(cpptoc PRIVATE ${LLVM_DEFINITIONS})

# Add LLVM/Clang include directories to target (modern CMake practice)
target_include_directories(cpptoc PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

# Link against Clang/LLVM libraries
# Minimal set needed for LibTooling
# Note: Order matters - most dependent first
target_link_libraries(cpptoc PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Test Executables (Epic #2 and Epic #3)
# ============================================================================

# Story #15: CppToCVisitor tests
add_executable(CppToCVisitorTest
    tests/CppToCVisitorTest.cpp
    src/CppToCVisitor.cpp
    src/CFGAnalyzer.cpp
    src/NameMangler.cpp
    src/CFGAnalyzer.cpp
    src/VirtualMethodAnalyzer.cpp
    src/VptrInjector.cpp
)

target_compile_definitions(CppToCVisitorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(CppToCVisitorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(CppToCVisitorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #18: NameMangler tests
add_executable(NameManglerTest
    tests/NameManglerTest.cpp
    src/NameMangler.cpp
)

target_compile_definitions(NameManglerTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(NameManglerTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(NameManglerTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #66: Overload Resolution via Parameter Type Encoding tests
add_executable(OverloadResolutionTest
    tests/OverloadResolutionTest.cpp
    src/NameMangler.cpp
)

target_compile_definitions(OverloadResolutionTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(OverloadResolutionTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(OverloadResolutionTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #67: Template Instantiation Extraction tests
add_executable(TemplateExtractorTest
    tests/TemplateExtractorTest.cpp
    src/TemplateExtractor.cpp
)

target_compile_definitions(TemplateExtractorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(TemplateExtractorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(TemplateExtractorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #68: Template Monomorphization and Code Generation tests
add_executable(MonomorphizationTest
    tests/MonomorphizationTest.cpp
    src/TemplateMonomorphizer.cpp
    src/TemplateExtractor.cpp
    src/NameMangler.cpp
)

target_compile_definitions(MonomorphizationTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(MonomorphizationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(MonomorphizationTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #69: STL Container Support and Integration Testing
add_executable(STLIntegrationTest
    tests/STLIntegrationTest.cpp
    src/TemplateMonomorphizer.cpp
    src/TemplateExtractor.cpp
    src/NameMangler.cpp
)

target_compile_definitions(STLIntegrationTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(STLIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(STLIntegrationTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #20: Translation Integration Tests
add_executable(TranslationIntegrationTest
    tests/TranslationIntegrationTest.cpp
    src/CppToCVisitor.cpp
    src/CFGAnalyzer.cpp
    src/NameMangler.cpp
    src/VirtualMethodAnalyzer.cpp
    src/VptrInjector.cpp
)

target_compile_definitions(TranslationIntegrationTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(TranslationIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(TranslationIntegrationTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Epic #4: CodeGenerator Tests (Story #21)
# ============================================================================

# Story #21: CodeGenerator tests
add_executable(CodeGeneratorTest
    tests/CodeGeneratorTest.cpp
    src/CodeGenerator.cpp
)

target_compile_definitions(CodeGeneratorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(CodeGeneratorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(CodeGeneratorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Epic #4: Comprehensive Validation Tests (Stories #24, #25, #26)
# ============================================================================

# Stories #24-26: Compilation, Behavioral, and Memory Safety validation
add_executable(ValidationTest
    tests/ValidationTest.cpp
    src/CodeGenerator.cpp
    src/CppToCVisitor.cpp
    src/CFGAnalyzer.cpp
    src/NameMangler.cpp
    src/VirtualMethodAnalyzer.cpp
    src/VptrInjector.cpp
)

target_compile_definitions(ValidationTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(ValidationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(ValidationTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Epic #19: Header File Generation Tests (Story #137)
# ============================================================================

# Story #137: Header/Implementation Separation tests
add_executable(HeaderSeparatorTest
    tests/HeaderSeparatorTest.cpp
    src/HeaderSeparator.cpp
)

target_compile_definitions(HeaderSeparatorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(HeaderSeparatorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(HeaderSeparatorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #138: Include Guard Generation tests
add_executable(IncludeGuardGeneratorTest
    tests/IncludeGuardGeneratorTest.cpp
    src/IncludeGuardGenerator.cpp
)

target_compile_definitions(IncludeGuardGeneratorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(IncludeGuardGeneratorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(IncludeGuardGeneratorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #139: Forward Declaration Support tests
add_executable(ForwardDeclTest
    tests/ForwardDeclTest.cpp
    src/HeaderSeparator.cpp
)

target_compile_definitions(ForwardDeclTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(ForwardDeclTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(ForwardDeclTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #140: Dependency Tracking tests
add_executable(DependencyAnalyzerTest
    tests/DependencyAnalyzerTest.cpp
    src/DependencyAnalyzer.cpp
)

target_compile_definitions(DependencyAnalyzerTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(DependencyAnalyzerTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(DependencyAnalyzerTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #141: File Output System tests
add_executable(FileOutputManagerTest
    tests/FileOutputManagerTest.cpp
    src/FileOutputManager.cpp
)

target_compile_definitions(FileOutputManagerTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(FileOutputManagerTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(FileOutputManagerTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #142: Integration Testing
add_executable(IntegrationTest
    tests/IntegrationTest.cpp
    src/HeaderSeparator.cpp
    src/IncludeGuardGenerator.cpp
    src/DependencyAnalyzer.cpp
    src/FileOutputManager.cpp
)

target_compile_definitions(IntegrationTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(IntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(IntegrationTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Epic #5: RAII + Automatic Destructor Injection (Story #151)
# ============================================================================

# Story #151: CFG Analysis Infrastructure tests
add_executable(CFGAnalysisTest
    tests/CFGAnalysisTest.cpp
    src/CFGAnalyzer.cpp
)

target_compile_definitions(CFGAnalysisTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(CFGAnalysisTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(CFGAnalysisTest PRIVATE
    clangTooling
    clangFrontend
    clangAnalysis
    clangAST
    clangBasic
)

# Story #152: Destructor Injection at Function Exit tests
add_executable(FunctionExitDestructorTest
    tests/FunctionExitDestructorTest.cpp
    src/CppToCVisitor.cpp
    src/CFGAnalyzer.cpp
    src/NameMangler.cpp
    src/CFGAnalyzer.cpp
    src/VirtualMethodAnalyzer.cpp
    src/VptrInjector.cpp
)

target_compile_definitions(FunctionExitDestructorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(FunctionExitDestructorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(FunctionExitDestructorTest PRIVATE
    clangTooling
    clangFrontend
    clangAnalysis
    clangAST
    clangBasic
)

# Story #153: Destructor Injection at Early Returns tests
add_executable(EarlyReturnDestructorTest
    tests/EarlyReturnDestructorTest.cpp
    src/CFGAnalyzer.cpp
)

target_compile_definitions(EarlyReturnDestructorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(EarlyReturnDestructorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(EarlyReturnDestructorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #154: Nested Scope Destruction tests
add_executable(NestedScopeDestructorTest
    tests/NestedScopeDestructorTest.cpp
    src/CFGAnalyzer.cpp
)

target_compile_definitions(NestedScopeDestructorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(NestedScopeDestructorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(NestedScopeDestructorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #155: Goto Statement Handling tests
add_executable(GotoDestructorTest
    tests/GotoDestructorTest.cpp
    src/CFGAnalyzer.cpp
)

target_compile_definitions(GotoDestructorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(GotoDestructorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(GotoDestructorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #156: Loop Break/Continue Handling tests
add_executable(LoopDestructorTest
    tests/LoopDestructorTest.cpp
    src/CFGAnalyzer.cpp
)

target_compile_definitions(LoopDestructorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(LoopDestructorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(LoopDestructorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #157: Integration Testing & Validation
add_executable(RAIIIntegrationTest
    tests/RAIIIntegrationTest.cpp
    src/CFGAnalyzer.cpp
)

target_compile_definitions(RAIIIntegrationTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(RAIIIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(RAIIIntegrationTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Epic #6: Single Inheritance Support (Story #50)
# ============================================================================

# Story #50: Base Class Embedding in Struct Layout tests
add_executable(InheritanceTest
    tests/InheritanceTest.cpp
    src/CppToCVisitor.cpp
    src/CFGAnalyzer.cpp
    src/NameMangler.cpp
    src/VirtualMethodAnalyzer.cpp
    src/VptrInjector.cpp
)

target_compile_definitions(InheritanceTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(InheritanceTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(InheritanceTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Epic #41: Virtual Functions + Vtables (Story #167)
# ============================================================================

# Story #167: Virtual Method Detection and AST Analysis tests
add_executable(VirtualMethodAnalyzerTest
    tests/VirtualMethodAnalyzerTest.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(VirtualMethodAnalyzerTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(VirtualMethodAnalyzerTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(VirtualMethodAnalyzerTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #168: Vtable Struct Generation tests
add_executable(VtableGeneratorTest
    tests/VtableGeneratorTest.cpp
    src/VtableGenerator.cpp
    src/VirtualMethodAnalyzer.cpp
    src/OverrideResolver.cpp
)

target_compile_definitions(VtableGeneratorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(VtableGeneratorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(VtableGeneratorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #169: Vptr Field Injection in Class Layout tests
add_executable(VptrInjectorTest
    tests/VptrInjectorTest.cpp
    src/VptrInjector.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(VptrInjectorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(VptrInjectorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(VptrInjectorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #170: Virtual Function Override Resolution tests
add_executable(OverrideResolverTest
    tests/OverrideResolverTest.cpp
    src/OverrideResolver.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(OverrideResolverTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(OverrideResolverTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(OverrideResolverTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #171: Vtable Initialization in Constructors tests
add_executable(VtableInitializerTest
    tests/VtableInitializerTest.cpp
    src/VtableInitializer.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(VtableInitializerTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(VtableInitializerTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(VtableInitializerTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #172: Virtual Call Translation to Vtable Dispatch tests
add_executable(VirtualCallTranslatorTest
    tests/VirtualCallTranslatorTest.cpp
    src/VirtualCallTranslator.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(VirtualCallTranslatorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(VirtualCallTranslatorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(VirtualCallTranslatorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #173: Pure Virtual Function Support tests
add_executable(PureVirtualHandlerTest
    tests/PureVirtualHandlerTest.cpp
    src/PureVirtualHandler.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(PureVirtualHandlerTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(PureVirtualHandlerTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(PureVirtualHandlerTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #174: Virtual Destructor Handling tests
add_executable(VirtualDestructorHandlerTest
    tests/VirtualDestructorHandlerTest.cpp
    src/VirtualDestructorHandler.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(VirtualDestructorHandlerTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(VirtualDestructorHandlerTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(VirtualDestructorHandlerTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #175: Comprehensive Virtual Function Integration Tests
add_executable(VirtualFunctionIntegrationTest
    tests/VirtualFunctionIntegrationTest.cpp
    src/VirtualMethodAnalyzer.cpp
    src/VtableGenerator.cpp
    src/VptrInjector.cpp
    src/OverrideResolver.cpp
    src/VtableInitializer.cpp
    src/VirtualCallTranslator.cpp
    src/PureVirtualHandler.cpp
    src/VirtualDestructorHandler.cpp
)

target_compile_definitions(VirtualFunctionIntegrationTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(VirtualFunctionIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(VirtualFunctionIntegrationTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Epic #7: Advanced Constructor/Destructor Features (Story #178)
# ============================================================================

# Story #178: Member Initialization List Translation tests
add_executable(MemberInitListTest
    tests/MemberInitListTest.cpp
    src/CppToCVisitor.cpp
    src/CFGAnalyzer.cpp
    src/NameMangler.cpp
    src/VirtualMethodAnalyzer.cpp
    src/VptrInjector.cpp
    src/CodeGenerator.cpp
)

target_compile_definitions(MemberInitListTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(MemberInitListTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(MemberInitListTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Epic #10: Exception Handling (PNaCl SJLJ) (Story #76)
# ============================================================================

# Story #76: Exception Frame Structure and Thread-Local Stack tests
add_executable(ExceptionFrameTest
    tests/ExceptionFrameTest.cpp
    src/ExceptionFrameGenerator.cpp
)

target_compile_definitions(ExceptionFrameTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(ExceptionFrameTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(ExceptionFrameTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #77: Action Table Generation from CFG Analysis tests
add_executable(ActionTableGeneratorTest
    tests/ActionTableGeneratorTest.cpp
    src/ActionTableGenerator.cpp
)

target_compile_definitions(ActionTableGeneratorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(ActionTableGeneratorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(ActionTableGeneratorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #78: setjmp/longjmp Injection for Try-Catch Blocks tests
add_executable(TryCatchTransformerTest
    tests/TryCatchTransformerTest.cpp
    src/TryCatchTransformer.cpp
    src/ExceptionFrameGenerator.cpp
)

target_compile_definitions(TryCatchTransformerTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(TryCatchTransformerTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(TryCatchTransformerTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #79: Throw Expression Translation tests
add_executable(ThrowTranslatorTest
    tests/ThrowTranslatorTest.cpp
    src/ThrowTranslator.cpp
)

target_compile_definitions(ThrowTranslatorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(ThrowTranslatorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(ThrowTranslatorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #80: Catch Handler Type Matching tests
add_executable(CatchHandlerTypeMatchingTest
    tests/CatchHandlerTypeMatchingTest.cpp
    src/TryCatchTransformer.cpp
    src/ExceptionFrameGenerator.cpp
)

target_compile_definitions(CatchHandlerTypeMatchingTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(CatchHandlerTypeMatchingTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(CatchHandlerTypeMatchingTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #81: Exception Runtime Library tests
add_executable(ExceptionRuntimeTest
    tests/ExceptionRuntimeTest.cpp
    runtime/exception_runtime.cpp
)

target_include_directories(ExceptionRuntimeTest PRIVATE
    ${CMAKE_SOURCE_DIR}/runtime
)

# Set C11 standard for thread-local storage
set_property(TARGET ExceptionRuntimeTest PROPERTY C_STANDARD 11)
set_property(TARGET ExceptionRuntimeTest PROPERTY C_STANDARD_REQUIRED ON)

# No Clang/LLVM dependencies - pure C runtime library

# Story #82: Exception Integration Tests
add_executable(ExceptionIntegrationTest
    tests/ExceptionIntegrationTest.cpp
    runtime/exception_runtime.cpp
)

target_include_directories(ExceptionIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/runtime
)

# Story #82: Exception Thread Safety Tests
add_executable(ExceptionThreadSafetyTest
    tests/ExceptionThreadSafetyTest.cpp
    runtime/exception_runtime.cpp
)

target_include_directories(ExceptionThreadSafetyTest PRIVATE
    ${CMAKE_SOURCE_DIR}/runtime
)

# Link pthread for thread safety tests
find_package(Threads REQUIRED)
target_link_libraries(ExceptionThreadSafetyTest PRIVATE Threads::Threads)

# Story #82: Exception Performance Benchmarks
add_executable(ExceptionPerformanceTest
    tests/ExceptionPerformanceTest.cpp
    runtime/exception_runtime.cpp
)

target_include_directories(ExceptionPerformanceTest PRIVATE
    ${CMAKE_SOURCE_DIR}/runtime
)

# ============================================================================
# Epic #11: RTTI Implementation (Itanium ABI) (Story #83)
# ============================================================================

# Story #83: type_info Structure Generation tests
add_executable(TypeInfoGeneratorTest
    tests/TypeInfoGeneratorTest.cpp
    src/TypeInfoGenerator.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(TypeInfoGeneratorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(TypeInfoGeneratorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(TypeInfoGeneratorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #84: typeid Operator Translation tests
add_executable(TypeidTranslatorTest
    tests/TypeidTranslatorTest.cpp
    src/TypeidTranslator.cpp
    src/TypeInfoGenerator.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(TypeidTranslatorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(TypeidTranslatorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(TypeidTranslatorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #85: dynamic_cast Downcast Support tests
add_executable(DynamicCastTranslatorTest
    tests/DynamicCastTranslatorTest.cpp
    src/DynamicCastTranslator.cpp
    src/TypeInfoGenerator.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(DynamicCastTranslatorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(DynamicCastTranslatorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(DynamicCastTranslatorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #86: Hierarchy Traversal Algorithm tests
add_executable(HierarchyTraversalTest
    tests/HierarchyTraversalTest.cpp
    runtime/rtti_runtime.c
)

target_include_directories(HierarchyTraversalTest PRIVATE
    ${CMAKE_SOURCE_DIR}/runtime
)

# No Clang/LLVM dependencies - pure C runtime library

# Story #87: dynamic_cast Cross-Casting Support tests
add_executable(DynamicCastCrossCastTest
    tests/DynamicCastCrossCastTest.cpp
    src/DynamicCastTranslator.cpp
    src/TypeInfoGenerator.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(DynamicCastCrossCastTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(DynamicCastCrossCastTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(DynamicCastCrossCastTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #87: Cross-Cast Hierarchy Traversal tests
add_executable(CrossCastTraversalTest
    tests/CrossCastTraversalTest.cpp
    runtime/rtti_runtime.c
)

target_include_directories(CrossCastTraversalTest PRIVATE
    ${CMAKE_SOURCE_DIR}/runtime
)

# No Clang/LLVM dependencies - pure C runtime library

# Story #89: Virtual Base Detection and Analysis tests (Epic #44)
add_executable(VirtualBaseDetectionTest
    tests/VirtualBaseDetectionTest.cpp
    src/VirtualInheritanceAnalyzer.cpp
)

target_compile_definitions(VirtualBaseDetectionTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(VirtualBaseDetectionTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(VirtualBaseDetectionTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
    clangASTMatchers
)

# Story #90: Virtual Base Offset Table Generation tests (Epic #44)
add_executable(VirtualBaseOffsetTableTest
    tests/VirtualBaseOffsetTableTest.cpp
    src/VtableGenerator.cpp
    src/VirtualMethodAnalyzer.cpp
    src/VirtualInheritanceAnalyzer.cpp
    src/OverrideResolver.cpp
)

target_compile_definitions(VirtualBaseOffsetTableTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(VirtualBaseOffsetTableTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(VirtualBaseOffsetTableTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
    clangASTMatchers
)

# Story #91: VTT (Virtual Table Tables) Generation tests (Epic #44)
add_executable(VTTGeneratorTest
    tests/VTTGeneratorTest.cpp
    src/VTTGenerator.cpp
    src/VirtualInheritanceAnalyzer.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(VTTGeneratorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(VTTGeneratorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(VTTGeneratorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
    clangASTMatchers
)

# Story #92: Constructor Splitting (C1/C2 Variants) tests (Epic #44)
add_executable(ConstructorSplitterTest
    tests/ConstructorSplitterTest.cpp
    src/ConstructorSplitter.cpp
    src/VirtualInheritanceAnalyzer.cpp
    src/VirtualMethodAnalyzer.cpp
)

target_compile_definitions(ConstructorSplitterTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(ConstructorSplitterTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(ConstructorSplitterTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #102: Coroutine Detection and Frame Structure tests (Epic #46)
add_executable(CoroutineDetectorTest
    tests/CoroutineDetectorTest.cpp
    src/CoroutineDetector.cpp
)

target_compile_definitions(CoroutineDetectorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(CoroutineDetectorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(CoroutineDetectorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #103: Suspend Point Identification tests (Epic #46)
add_executable(SuspendPointIdentifierTest
    tests/SuspendPointIdentifierTest.cpp
    src/SuspendPointIdentifier.cpp
)

target_compile_definitions(SuspendPointIdentifierTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(SuspendPointIdentifierTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(SuspendPointIdentifierTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #104: State Machine Transformation tests (Epic #46)
add_executable(StateMachineTransformerTest
    tests/StateMachineTransformerTest.cpp
    src/StateMachineTransformer.cpp
    src/SuspendPointIdentifier.cpp
)

target_compile_definitions(StateMachineTransformerTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(StateMachineTransformerTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(StateMachineTransformerTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
    clangLex
)

# Story #105: Promise Object Translation tests (Epic #46)
add_executable(PromiseTranslatorTest
    tests/PromiseTranslatorTest.cpp
    src/PromiseTranslator.cpp
)

target_compile_definitions(PromiseTranslatorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(PromiseTranslatorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(PromiseTranslatorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #106: Resume and Destroy Function Generation tests (Epic #46)
add_executable(ResumeDestroyFunctionTest
    tests/ResumeDestroyFunctionTest.cpp
    src/StateMachineTransformer.cpp
    src/SuspendPointIdentifier.cpp
)

target_compile_definitions(ResumeDestroyFunctionTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(ResumeDestroyFunctionTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(ResumeDestroyFunctionTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
    clangLex
)

# Story #107: Frame Allocation and Coroutine Handle tests (Epic #46)
add_executable(FrameAllocationTest
    tests/FrameAllocationTest.cpp
    src/FrameAllocator.cpp
)

target_compile_definitions(FrameAllocationTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(FrameAllocationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(FrameAllocationTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #108: Integration Testing tests (Epic #46)
add_executable(CoroutineIntegrationTest
    tests/CoroutineIntegrationTest.cpp
    src/CoroutineDetector.cpp
    src/SuspendPointIdentifier.cpp
    src/StateMachineTransformer.cpp
    src/PromiseTranslator.cpp
    src/FrameAllocator.cpp
)

target_compile_definitions(CoroutineIntegrationTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(CoroutineIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(CoroutineIntegrationTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
    clangLex
)

# ============================================================================
# Epic #16: Runtime Optimization & Configuration (Story #116)
# ============================================================================

# Story #116: Inline Runtime Mode tests
add_executable(RuntimeModeInlineTest
    tests/runtime_mode_inline_test.cpp
    src/RuntimeModeInline.cpp
)

target_compile_definitions(RuntimeModeInlineTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(RuntimeModeInlineTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(RuntimeModeInlineTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Story #117: Library Runtime Mode tests
add_executable(RuntimeModeLibraryTest
    tests/runtime_mode_library_test.cpp
    src/RuntimeModeLibrary.cpp
)

target_include_directories(RuntimeModeLibraryTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
)

# Story #118: Runtime Feature Flags tests
add_executable(RuntimeFeatureFlagsTest
    tests/runtime_feature_flags_test.cpp
    src/RuntimeFeatureFlags.cpp
)

target_include_directories(RuntimeFeatureFlagsTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
)

# Story #119: Size Optimization with LTO/PGO Support tests
add_executable(SizeOptimizationTest
    tests/size_optimization_test.cpp
    src/SizeOptimizer.cpp
    src/BuildConfiguration.cpp
)

target_include_directories(SizeOptimizationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
)

# ============================================================================
# Stream 4: Operator Overloading Tests (62 tests)
# ============================================================================

# Comprehensive operator overloading tests covering all operator categories
add_executable(OperatorOverloadingTest
    tests/unit/operators/OperatorOverloadingTest.cpp
    src/NameMangler.cpp
)

target_compile_definitions(OperatorOverloadingTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(OperatorOverloadingTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(OperatorOverloadingTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Stream 1: Lambdas & Closures Tests (60 tests)
# ============================================================================

# Lambda Translation and Closure Generation tests
add_executable(LambdaTranslatorTest
    tests/unit/lambdas/LambdaTranslatorTest.cpp
)

target_compile_definitions(LambdaTranslatorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(LambdaTranslatorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(LambdaTranslatorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Stream 2: Move Semantics & Perfect Forwarding Tests (50 tests)
# ============================================================================

add_executable(MoveSemanticTranslatorTest
    tests/unit/move_semantics/MoveSemanticTranslatorTest.cpp
)

target_compile_definitions(MoveSemanticTranslatorTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(MoveSemanticTranslatorTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(MoveSemanticTranslatorTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Stream 5: Type Traits & Template Metaprogramming Tests (85 tests)
# ============================================================================

# TypeTraitsTest - 40 tests for type traits, SFINAE, and compile-time conditionals
add_executable(TypeTraitsTest
    tests/unit/type_traits/TypeTraitsTest.cpp
)

target_compile_definitions(TypeTraitsTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(TypeTraitsTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(TypeTraitsTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# MetaprogrammingTest - 45 tests for variadic templates, constexpr, and recursive metaprogramming
add_executable(MetaprogrammingTest
    tests/unit/type_traits/MetaprogrammingTest.cpp
)

target_compile_definitions(MetaprogrammingTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(MetaprogrammingTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(MetaprogrammingTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Stream 6: Edge Cases & Integration Tests (75 tests)
# ============================================================================

# EdgeCasesTest - 30 tests for boundary conditions
add_executable(EdgeCasesTest
    tests/integration/EdgeCasesTest.cpp
)

target_compile_definitions(EdgeCasesTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(EdgeCasesTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(EdgeCasesTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ErrorHandlingTest - 25 tests for error handling
add_executable(ErrorHandlingTest
    tests/integration/ErrorHandlingTest.cpp
)

target_compile_definitions(ErrorHandlingTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(ErrorHandlingTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(ErrorHandlingTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# FeatureInteractionTest - 30 tests for feature interactions
add_executable(FeatureInteractionTest
    tests/integration/FeatureInteractionTest.cpp
)

target_compile_definitions(FeatureInteractionTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(FeatureInteractionTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(FeatureInteractionTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# FeatureCombinationTest - 20 tests for complex feature combinations
# Story #123: Integration Test Suite (RAII+exceptions, virtual inheritance+RTTI,
# multiple inheritance+virtual, coroutines+RAII, complex hierarchies, kitchen sink)
add_executable(FeatureCombinationTest
    tests/integration/FeatureCombinationTest.cpp
)

target_compile_definitions(FeatureCombinationTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(FeatureCombinationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(FeatureCombinationTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# ============================================================================
# Stream 3: Smart Pointers & RAII Tests (95 tests)
# ============================================================================

# File 1: UniquePtrTest.cpp (30 tests)
# unique_ptr creation, moves, make_unique, custom deleters
add_executable(UniquePtrTest
    tests/unit/smart_pointers/UniquePtrTest.cpp
)

target_compile_definitions(UniquePtrTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(UniquePtrTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(UniquePtrTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# File 2: SharedPtrTest.cpp (40 tests)
# shared_ptr, ref counting, make_shared, weak_ptr, thread-safety
add_executable(SharedPtrTest
    tests/unit/smart_pointers/SharedPtrTest.cpp
)

target_compile_definitions(SharedPtrTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(SharedPtrTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(SharedPtrTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# File 3: RaiiIntegrationTest.cpp (25 tests)
# Smart pointers with RAII (file, network, locks), exception safety
add_executable(SmartPointerRaiiIntegrationTest
    tests/unit/smart_pointers/RaiiIntegrationTest.cpp
)

target_compile_definitions(SmartPointerRaiiIntegrationTest PRIVATE ${LLVM_DEFINITIONS})

target_include_directories(SmartPointerRaiiIntegrationTest PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

target_link_libraries(SmartPointerRaiiIntegrationTest PRIVATE
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)

# Build runtime library subdirectory
add_subdirectory(runtime)

# ============================================================================
# Benchmarks (Optional)
# ============================================================================
# Performance benchmarks are optional and controlled by BUILD_BENCHMARKS flag
# To build benchmarks: cmake -B build -DBUILD_BENCHMARKS=ON
add_subdirectory(benchmarks)
