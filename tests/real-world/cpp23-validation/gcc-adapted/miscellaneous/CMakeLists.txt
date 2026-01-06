cmake_minimum_required(VERSION 3.12)

project(miscellaneous-cpp23-tests)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Test sources
set(TEST_SOURCES
    test01.cpp
    test02.cpp
    test03.cpp
    test04.cpp
    test05.cpp
    test06.cpp
    test07.cpp
    test08.cpp
    test09.cpp
    test10.cpp
    test11.cpp
    test12.cpp
    test13.cpp
    test14.cpp
    test15.cpp
    test16.cpp
    test17.cpp
    test18.cpp
    test19.cpp
)

# For each test file, create an executable
foreach(test_file ${TEST_SOURCES})
    get_filename_component(test_name ${test_file} NAME_WE)
    add_executable(${test_name} ${test_file})
    set_target_properties(${test_name} PROPERTIES
        CXX_STANDARD 23
        CXX_STANDARD_REQUIRED ON
    )
    add_test(NAME ${test_name} COMMAND ${test_name})
endforeach()

enable_testing()
