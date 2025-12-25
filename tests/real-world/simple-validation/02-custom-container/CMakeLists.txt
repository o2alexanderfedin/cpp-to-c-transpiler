cmake_minimum_required(VERSION 3.10)
project(CustomContainer CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

include_directories(include)

add_executable(custom_container
    main.cpp
)
