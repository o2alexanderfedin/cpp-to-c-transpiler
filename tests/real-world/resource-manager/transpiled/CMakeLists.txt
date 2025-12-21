cmake_minimum_required(VERSION 3.20)
project(resource_manager_c C)

# C11 standard required for ACSL annotations and modern C features
set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS ON)  # For GCC cleanup attribute

# Compiler flags for strict checking
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Wextra -Werror -pedantic")
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wno-unused-parameter")  # ACSL annotations may have unused params

# Debug build settings
set(CMAKE_C_FLAGS_DEBUG "${CMAKE_C_FLAGS_DEBUG} -g -O0 -fsanitize=address,undefined")
set(CMAKE_EXE_LINKER_FLAGS_DEBUG "${CMAKE_EXE_LINKER_FLAGS_DEBUG} -fsanitize=address,undefined")

# Release build settings
set(CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE} -O3 -DNDEBUG")

# Resource manager library
add_library(resource_manager STATIC
    resource_manager.c
    resource_manager.h
)

target_include_directories(resource_manager PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
)

# Test executable (if we create one)
# Uncomment when test file is created
# add_executable(test_resource_manager_c
#     test_resource_manager.c
# )
#
# target_link_libraries(test_resource_manager_c
#     resource_manager
# )

# Enable testing
enable_testing()

# ACSL verification targets (requires Frama-C)
find_program(FRAMAC frama-c)
if(FRAMAC)
    message(STATUS "Found Frama-C: ${FRAMAC}")

    # ACSL syntax validation
    add_custom_target(verify_acsl
        COMMAND ${FRAMAC} -cpp-extra-args="-I${CMAKE_CURRENT_SOURCE_DIR}"
                ${CMAKE_CURRENT_SOURCE_DIR}/resource_manager.h
                ${CMAKE_CURRENT_SOURCE_DIR}/resource_manager.c
        COMMENT "Validating ACSL annotations with Frama-C"
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    )

    # WP (Weakest Precondition) verification
    add_custom_target(verify_wp
        COMMAND ${FRAMAC} -wp -wp-prover alt-ergo,cvc4,z3
                -cpp-extra-args="-I${CMAKE_CURRENT_SOURCE_DIR}"
                ${CMAKE_CURRENT_SOURCE_DIR}/resource_manager.c
        COMMENT "Running WP verification on resource_manager.c"
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    )

    # Value analysis
    add_custom_target(verify_value
        COMMAND ${FRAMAC} -val
                -cpp-extra-args="-I${CMAKE_CURRENT_SOURCE_DIR}"
                ${CMAKE_CURRENT_SOURCE_DIR}/resource_manager.c
        COMMENT "Running value analysis on resource_manager.c"
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    )
else()
    message(STATUS "Frama-C not found - ACSL verification targets disabled")
    message(STATUS "Install Frama-C to enable formal verification")
endif()

# Installation
install(TARGETS resource_manager
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
)

install(FILES resource_manager.h
    DESTINATION include
)

# Print configuration summary
message(STATUS "")
message(STATUS "===== Resource Manager C Transpilation =====")
message(STATUS "C Standard: C${CMAKE_C_STANDARD}")
message(STATUS "Build Type: ${CMAKE_BUILD_TYPE}")
message(STATUS "C Compiler: ${CMAKE_C_COMPILER}")
message(STATUS "C Flags: ${CMAKE_C_FLAGS}")
message(STATUS "Frama-C: ${FRAMAC}")
message(STATUS "===========================================")
message(STATUS "")
