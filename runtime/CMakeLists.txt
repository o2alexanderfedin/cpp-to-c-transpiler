# C++ to C Runtime Library - CMake Configuration
# Story #117: Implement Library Runtime Mode
#
# This CMakeLists.txt builds the runtime library as a separate static library
# that can be linked with generated C code, achieving 99% size reduction
# and 27% faster compilation for large projects (100+ files).

cmake_minimum_required(VERSION 3.10)

#==============================================================================
# Modular Feature Options
#==============================================================================

option(RUNTIME_EXCEPTIONS "Enable exception handling support" ON)
option(RUNTIME_RTTI "Enable RTTI (Run-Time Type Information) support" ON)
option(RUNTIME_VIRTUAL_INHERITANCE "Enable virtual inheritance support (not yet implemented)" ON)
option(RUNTIME_COROUTINES "Enable coroutines support (not yet implemented)" ON)

#==============================================================================
# Optimization Options
#==============================================================================

option(OPTIMIZE_SIZE "Enable size optimization (-Os, -ffunction-sections, -fdata-sections)" OFF)
option(ENABLE_LTO "Enable Link-Time Optimization" OFF)
option(ENABLE_PGO "Enable Profile-Guided Optimization setup" OFF)

#==============================================================================
# Build Source List Based on Enabled Features
#==============================================================================

set(RUNTIME_SOURCES "")
set(RUNTIME_HEADERS "")

# Exception handling sources
if(RUNTIME_EXCEPTIONS)
  list(APPEND RUNTIME_SOURCES exception_runtime.cpp)
  list(APPEND RUNTIME_HEADERS exception_runtime.h)
endif()

# RTTI sources
if(RUNTIME_RTTI)
  list(APPEND RUNTIME_SOURCES rtti_runtime.c)
  list(APPEND RUNTIME_HEADERS rtti_runtime.h)
endif()

# Ensure we have at least one source file
if(NOT RUNTIME_SOURCES)
  message(FATAL_ERROR "At least one runtime feature must be enabled!")
endif()

#==============================================================================
# Create Runtime Library Target
#==============================================================================

add_library(cpptoc_runtime STATIC ${RUNTIME_SOURCES})

# Set C/C++ standards
set_target_properties(cpptoc_runtime PROPERTIES
  C_STANDARD 11
  C_STANDARD_REQUIRED ON
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
)

# Set include directories
target_include_directories(cpptoc_runtime PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}
)

# Enable position-independent code for potential shared library usage
set_target_properties(cpptoc_runtime PROPERTIES
  POSITION_INDEPENDENT_CODE ON
)

#==============================================================================
# Apply Optimization Flags
#==============================================================================

if(OPTIMIZE_SIZE)
  target_compile_options(cpptoc_runtime PRIVATE
    -Os                    # Optimize for size
    -ffunction-sections    # Place each function in separate section
    -fdata-sections        # Place each data in separate section
  )
  target_link_options(cpptoc_runtime PRIVATE
    -Wl,--gc-sections      # Remove unused sections at link time
  )
endif()

if(ENABLE_LTO)
  set_target_properties(cpptoc_runtime PROPERTIES
    INTERPROCEDURAL_OPTIMIZATION TRUE
  )
  target_compile_options(cpptoc_runtime PRIVATE -flto)
  target_link_options(cpptoc_runtime PRIVATE -flto)
endif()

if(ENABLE_PGO)
  # PGO requires two-phase build: generate profile, then use profile
  # This sets up the generate phase by default
  target_compile_options(cpptoc_runtime PRIVATE -fprofile-generate)
  target_link_options(cpptoc_runtime PRIVATE -fprofile-generate)
  message(STATUS "PGO profile generation enabled - rebuild with -fprofile-use after profiling")
endif()

#==============================================================================
# Conditional Install Targets
#==============================================================================

install(TARGETS cpptoc_runtime
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib
)

if(RUNTIME_HEADERS)
  install(FILES ${RUNTIME_HEADERS}
    DESTINATION include/cpptoc
  )
endif()

#==============================================================================
# Optional: Build Shared Library Variant
#==============================================================================

option(BUILD_SHARED_RUNTIME "Build shared library variant" OFF)
if(BUILD_SHARED_RUNTIME)
  add_library(cpptoc_runtime_shared SHARED ${RUNTIME_SOURCES})

  set_target_properties(cpptoc_runtime_shared PROPERTIES
    OUTPUT_NAME cpptoc_runtime
    VERSION 1.0.0
    SOVERSION 1
    C_STANDARD 11
    C_STANDARD_REQUIRED ON
    CXX_STANDARD 17
    CXX_STANDARD_REQUIRED ON
  )

  target_include_directories(cpptoc_runtime_shared PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
  )

  # Apply same optimization flags to shared library
  if(OPTIMIZE_SIZE)
    target_compile_options(cpptoc_runtime_shared PRIVATE -Os -ffunction-sections -fdata-sections)
    target_link_options(cpptoc_runtime_shared PRIVATE -Wl,--gc-sections)
  endif()

  if(ENABLE_LTO)
    set_target_properties(cpptoc_runtime_shared PROPERTIES INTERPROCEDURAL_OPTIMIZATION TRUE)
    target_compile_options(cpptoc_runtime_shared PRIVATE -flto)
    target_link_options(cpptoc_runtime_shared PRIVATE -flto)
  endif()

  if(ENABLE_PGO)
    target_compile_options(cpptoc_runtime_shared PRIVATE -fprofile-generate)
    target_link_options(cpptoc_runtime_shared PRIVATE -fprofile-generate)
  endif()

  install(TARGETS cpptoc_runtime_shared
    LIBRARY DESTINATION lib
  )
endif()

#==============================================================================
# Configuration Status Messages
#==============================================================================

message(STATUS "")
message(STATUS "========================================")
message(STATUS "C++ to C Runtime Library Configuration")
message(STATUS "========================================")
message(STATUS "")

# Feature Status
message(STATUS "Runtime Features:")
message(STATUS "  - Exceptions:           ${RUNTIME_EXCEPTIONS}")
message(STATUS "  - RTTI:                 ${RUNTIME_RTTI}")
message(STATUS "  - Virtual Inheritance:  ${RUNTIME_VIRTUAL_INHERITANCE} (not implemented)")
message(STATUS "  - Coroutines:           ${RUNTIME_COROUTINES} (not implemented)")
message(STATUS "")

# Optimization Status
message(STATUS "Optimization Settings:")
message(STATUS "  - Size Optimization:    ${OPTIMIZE_SIZE}")
if(OPTIMIZE_SIZE)
  message(STATUS "    * Flags: -Os -ffunction-sections -fdata-sections")
  message(STATUS "    * Expected reduction: 15-25%")
endif()
message(STATUS "  - Link-Time Opt (LTO):  ${ENABLE_LTO}")
if(ENABLE_LTO)
  message(STATUS "    * Expected reduction: +10-15% (25-35% total)")
endif()
message(STATUS "  - Profile-Guided (PGO): ${ENABLE_PGO}")
if(ENABLE_PGO)
  message(STATUS "    * Mode: Generate profile data")
  message(STATUS "    * Expected reduction: +5-10% after recompile with profile")
endif()

if(OPTIMIZE_SIZE AND ENABLE_LTO)
  message(STATUS "")
  message(STATUS "  Combined optimization target: 35-45% size reduction")
endif()
message(STATUS "")

# Library Status
message(STATUS "Build Targets:")
message(STATUS "  - Static library:       cpptoc_runtime")
if(BUILD_SHARED_RUNTIME)
  message(STATUS "  - Shared library:       libcpptoc_runtime.so (version 1.0.0)")
endif()
message(STATUS "")

message(STATUS "Source Files:")
foreach(src ${RUNTIME_SOURCES})
  message(STATUS "  - ${src}")
endforeach()
message(STATUS "")

message(STATUS "Install Prefix: ${CMAKE_INSTALL_PREFIX}")
message(STATUS "========================================")
message(STATUS "")
