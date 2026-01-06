cmake_minimum_required(VERSION 3.10)
project(GameLogic CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

include_directories(include)

add_executable(game_logic
    src/Entity.cpp
    src/Player.cpp
    src/Enemy.cpp
    src/CollisionDetector.cpp
    main.cpp
)
