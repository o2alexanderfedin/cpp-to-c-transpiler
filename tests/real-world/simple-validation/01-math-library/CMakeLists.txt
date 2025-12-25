cmake_minimum_required(VERSION 3.10)
project(MathLibrary CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

include_directories(include)

add_executable(math_library
    src/Vector3D.cpp
    src/Matrix3x3.cpp
    main.cpp
)

target_link_libraries(math_library m)
