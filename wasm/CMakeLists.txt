cmake_minimum_required(VERSION 3.20)
project(cpptoc_wasm)

# Detect Emscripten build
if(EMSCRIPTEN)
    message(STATUS "Building for WebAssembly with Emscripten")
    message(STATUS "Using REAL Clang LibTooling transpiler")

    # Find Clang/LLVM for WASM build
    find_package(LLVM REQUIRED CONFIG)
    find_package(Clang REQUIRED CONFIG)

    # Enable C++ exceptions (required for try/catch)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fexceptions")

    # Common WASM linker flags (as a single string, space-separated)
    set(WASM_COMMON_FLAGS "\
-s MODULARIZE=1 \
-s EXPORT_ES6=1 \
-s EXPORT_NAME=createCppToC \
-s ALLOW_MEMORY_GROWTH=1 \
-s NO_FILESYSTEM=1 \
-s NO_EXIT_RUNTIME=1 \
-s WASM_ASYNC_COMPILATION=1 \
-s EXPORTED_RUNTIME_METHODS=['UTF8ToString','stringToUTF8'] \
--bind \
-s EXCEPTION_CATCHING_ALLOWED=['..'] \
-fexceptions")

    # ========================================================================
    # MINIMAL BUILD (Size-optimized for Cloudflare Workers)
    # ========================================================================
    add_executable(cpptoc-wasm-minimal
        bindings/minimal.cpp
        bindings/TranspilerAPIStub.cpp
    )

    target_include_directories(cpptoc-wasm-minimal PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/../include
    )

    target_compile_definitions(cpptoc-wasm-minimal PRIVATE
        EMSCRIPTEN
        WASM_MINIMAL_BUILD
    )

    # Minimal build: aggressive size optimization
    set_target_properties(cpptoc-wasm-minimal PROPERTIES
        LINK_FLAGS "${WASM_COMMON_FLAGS} -Oz --closure 1 -flto -s INITIAL_MEMORY=33554432 -s MAXIMUM_MEMORY=268435456 -s ASSERTIONS=0 -s STACK_OVERFLOW_CHECK=0 -s AGGRESSIVE_VARIABLE_ELIMINATION=1"
        OUTPUT_NAME "cpptoc-minimal"
    )

    # Generate TypeScript definitions for minimal build
    add_custom_command(TARGET cpptoc-wasm-minimal POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy
            ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-minimal.js
            ${CMAKE_CURRENT_SOURCE_DIR}/glue/dist/minimal/cpptoc.js
        COMMAND ${CMAKE_COMMAND} -E copy
            ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-minimal.wasm
            ${CMAKE_CURRENT_SOURCE_DIR}/glue/dist/minimal/cpptoc.wasm
        COMMENT "Copying minimal WASM artifacts to glue/dist"
    )

    # ========================================================================
    # FULL BUILD (Performance-optimized with all ACSL phases)
    # ========================================================================
    add_executable(cpptoc-wasm-full
        bindings/full.cpp
        # REAL TRANSPILER IMPLEMENTATION - ALL SOURCE FILES
        ../src/TranspilerAPI.cpp
        ../src/CppToCVisitor.cpp
        ../src/CFGAnalyzer.cpp
        ../src/NameMangler.cpp
        ../src/CodeGenerator.cpp
        ../src/ACSLGenerator.cpp
        ../src/ACSLFunctionAnnotator.cpp
        ../src/ACSLLoopAnnotator.cpp
        ../src/ACSLClassAnnotator.cpp
        ../src/ACSLStatementAnnotator.cpp
        ../src/ACSLTypeInvariantGenerator.cpp
        ../src/ACSLAxiomaticBuilder.cpp
        ../src/ACSLGhostCodeInjector.cpp
        ../src/ACSLBehaviorAnnotator.cpp
        ../src/ACSLMemoryPredicateAnalyzer.cpp
        ../src/HeaderSeparator.cpp
        ../src/IncludeGuardGenerator.cpp
        ../src/DependencyAnalyzer.cpp
        ../src/DependencyGraphVisualizer.cpp
        ../src/FileOutputManager.cpp
        ../src/VirtualMethodAnalyzer.cpp
        ../src/VptrInjector.cpp
        ../src/VirtualInheritanceAnalyzer.cpp
        ../src/MoveConstructorTranslator.cpp
        ../src/MoveAssignmentTranslator.cpp
        ../src/StdMoveTranslator.cpp
        ../src/RvalueRefParamTranslator.cpp
        ../src/VtableGenerator.cpp
        ../src/MethodSignatureHelper.cpp
        ../src/OverrideResolver.cpp
        ../src/VtableInitializer.cpp
    )

    target_include_directories(cpptoc-wasm-full PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/../include
        ${LLVM_INCLUDE_DIRS}
        ${CLANG_INCLUDE_DIRS}
    )

    target_compile_definitions(cpptoc-wasm-full PRIVATE
        ${LLVM_DEFINITIONS}
    )

    # Link Clang/LLVM libraries
    target_link_libraries(cpptoc-wasm-full PRIVATE
        clangTooling
        clangFrontend
        clangAST
        clangBasic
        LLVMSupport
    )

    # Full build: performance over size, increased memory for Clang
    # Using 64-bit WASM (MEMORY64) for much larger address space needed by Clang/LLVM
    set_target_properties(cpptoc-wasm-full PROPERTIES
        LINK_FLAGS "${WASM_COMMON_FLAGS} -O3 -sMEMORY64=2 -s INITIAL_MEMORY=268435456 -s MAXIMUM_MEMORY=4294967296 -s ASSERTIONS=1 -s STACK_OVERFLOW_CHECK=1 -s AGGRESSIVE_VARIABLE_ELIMINATION=1 -g1"
        OUTPUT_NAME "cpptoc-full"
    )

    # Generate TypeScript definitions for full build
    add_custom_command(TARGET cpptoc-wasm-full POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy
            ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-full.js
            ${CMAKE_CURRENT_SOURCE_DIR}/glue/dist/full/cpptoc.js
        COMMAND ${CMAKE_COMMAND} -E copy
            ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-full.wasm
            ${CMAKE_CURRENT_SOURCE_DIR}/glue/dist/full/cpptoc.wasm
        COMMENT "Copying full WASM artifacts to glue/dist"
    )

    # Install targets
    install(FILES
        ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-minimal.js
        ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-minimal.wasm
        DESTINATION wasm/minimal
    )

    install(FILES
        ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-full.js
        ${CMAKE_CURRENT_BINARY_DIR}/cpptoc-full.wasm
        DESTINATION wasm/full
    )
else()
    message(WARNING "Not building with Emscripten. WASM targets will be skipped.")
    message(STATUS "To build WASM: emcmake cmake -B build-wasm && emmake cmake --build build-wasm")
endif()
