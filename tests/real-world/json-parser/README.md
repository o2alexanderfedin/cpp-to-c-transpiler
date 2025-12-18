# JSON Parser - Real-World Test Project

## Overview
A minimal JSON parser implementation demonstrating real-world C++ features:
- RAII (Resource Acquisition Is Initialization)
- Exception handling for parse errors
- Recursive descent parsing
- Template usage for value types
- STL containers (map, vector, string)
- Polymorphism for JSON value types

## Target Size
1,000-1,500 lines of code

## C++ Features Tested
1. **Classes & Inheritance**: JsonValue, JsonObject, JsonArray, JsonString, JsonNumber, JsonBool, JsonNull
2. **RAII**: Automatic memory management, smart pointers
3. **Exceptions**: ParseError for invalid JSON
4. **Templates**: Visitor pattern for value traversal
5. **STL**: std::map, std::vector, std::string, std::unique_ptr
6. **Virtual Functions**: Polymorphic value types
7. **Operator Overloading**: [] operator for object/array access

## Validation Criteria
1. **Compilation**: Generated C code compiles without errors
2. **Functional**: Successfully parses valid JSON files
3. **Error Handling**: Properly rejects invalid JSON
4. **Memory Safety**: No memory leaks (valgrind clean)
5. **Performance**: Within 20% of native C++ performance

## Test Cases
- Simple objects: `{"key": "value"}`
- Nested objects: `{"outer": {"inner": 42}}`
- Arrays: `[1, 2, 3, "four"]`
- Mixed types: Numbers, strings, booleans, null
- Invalid JSON: Missing quotes, trailing commas, invalid syntax
