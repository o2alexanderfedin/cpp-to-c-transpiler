cmake_minimum_required(VERSION 3.10)
project(embedded-app-example CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Enable native build for testing on host system
option(NATIVE_BUILD "Build for native testing (not embedded)" ON)

if(NATIVE_BUILD)
    add_compile_definitions(NATIVE_BUILD=1)
endif()

# Source files
add_executable(embedded-app-test
    src/main.cpp
)

# Size optimization flags (embedded builds)
if(NOT NATIVE_BUILD)
    target_compile_options(embedded-app-test PRIVATE
        -Os                 # Optimize for size
        -fno-exceptions     # No exception handling
        -fno-rtti          # No RTTI
        -ffunction-sections # Allow dead code elimination
        -fdata-sections
    )

    target_link_options(embedded-app-test PRIVATE
        -Wl,--gc-sections  # Remove unused sections
    )
endif()

# Print size information
add_custom_command(TARGET embedded-app-test POST_BUILD
    COMMAND ${CMAKE_SIZE} $<TARGET_FILE:embedded-app-test>
    COMMENT "Size analysis:"
)
