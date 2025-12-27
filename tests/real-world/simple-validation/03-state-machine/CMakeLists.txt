cmake_minimum_required(VERSION 3.10)
project(StateMachine CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

include_directories(include)

add_executable(state_machine
    src/StateMachine.cpp
    main.cpp
)
