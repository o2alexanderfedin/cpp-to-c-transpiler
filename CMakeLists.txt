cmake_minimum_required(VERSION 3.20)
project(cpptoc C CXX)

# Set C++17 standard (SOLID principle: explicit requirements)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

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
    src/NameMangler.cpp
    src/CodeGenerator.cpp
    src/HeaderSeparator.cpp
    src/IncludeGuardGenerator.cpp
    src/DependencyAnalyzer.cpp
    src/FileOutputManager.cpp
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
    src/NameMangler.cpp
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

# Story #20: Translation Integration Tests
add_executable(TranslationIntegrationTest
    tests/TranslationIntegrationTest.cpp
    src/CppToCVisitor.cpp
    src/NameMangler.cpp
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
    src/NameMangler.cpp
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
