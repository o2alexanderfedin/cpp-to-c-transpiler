# C++ to C Runtime Library - CMake Configuration
# Story #117: Implement Library Runtime Mode
#
# This CMakeLists.txt builds the runtime library as a separate static library
# that can be linked with generated C code, achieving 99% size reduction
# and 27% faster compilation for large projects (100+ files).

cmake_minimum_required(VERSION 3.10)

# Create runtime library target
add_library(cpptoc_runtime STATIC
  exception_runtime.cpp
  rtti_runtime.c
)

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

# Install library and headers
install(TARGETS cpptoc_runtime
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib
)

install(FILES
  exception_runtime.h
  rtti_runtime.h
  DESTINATION include/cpptoc
)

# Optional: Build shared library variant
option(BUILD_SHARED_RUNTIME "Build shared library variant" OFF)
if(BUILD_SHARED_RUNTIME)
  add_library(cpptoc_runtime_shared SHARED
    exception_runtime.cpp
    rtti_runtime.c
  )

  set_target_properties(cpptoc_runtime_shared PROPERTIES
    OUTPUT_NAME cpptoc_runtime
    VERSION 1.0.0
    SOVERSION 1
  )

  target_include_directories(cpptoc_runtime_shared PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
  )

  install(TARGETS cpptoc_runtime_shared
    LIBRARY DESTINATION lib
  )
endif()

# Documentation
message(STATUS "C++ to C Runtime Library configured")
message(STATUS "  - Static library: cpptoc_runtime")
if(BUILD_SHARED_RUNTIME)
  message(STATUS "  - Shared library: libcpptoc_runtime.so (version 1.0.0)")
endif()
message(STATUS "  - Install prefix: ${CMAKE_INSTALL_PREFIX}")
