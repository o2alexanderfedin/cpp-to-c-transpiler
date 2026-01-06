#!/bin/bash

./build_working/cpptoc \
  --output-dir=./tests/real-world/transpiled \
  ./tests/real-world/json-parser/src/JsonParser.cpp \
  ./tests/real-world/json-parser/src/JsonValue.cpp \
  ./tests/real-world/json-parser/tests/examples.cpp \
  ./tests/real-world/json-parser/tests/test_json_parser.cpp \
  ./tests/real-world/logger/tests/examples.cpp \
  ./tests/real-world/logger/tests/test_logger.cpp \
  ./tests/real-world/resource-manager/tests/test_resource_manager.cpp \
  ./tests/real-world/string-formatter/tests/test_string_formatter.cpp \
  ./tests/real-world/test-framework/src/TestRegistry.cpp \
  ./tests/real-world/test-framework/tests/examples.cpp \
  ./tests/real-world/test-framework/tests/test_framework.cpp \
  -- \
  -I./tests/real-world/json-parser/include \
  -I./tests/real-world/logger/include \
  -I./tests/real-world/resource-manager/include \
  -I./tests/real-world/string-formatter/include \
  -I./tests/real-world/test-framework/include \
  -std=c++17
