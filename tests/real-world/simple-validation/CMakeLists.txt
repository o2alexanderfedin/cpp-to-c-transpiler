cmake_minimum_required(VERSION 3.10)
project(SimpleValidation CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_subdirectory(01-math-library)
add_subdirectory(02-custom-container)
add_subdirectory(03-state-machine)
add_subdirectory(04-simple-parser)
add_subdirectory(05-game-logic)
