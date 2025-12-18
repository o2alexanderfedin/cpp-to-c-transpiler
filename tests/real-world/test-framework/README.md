# Test Framework - Real-World Test Project

## Overview
Minimal unit test framework demonstrating:
- Macros for test assertions
- Templates for test fixtures
- Exception handling for failures
- RAII for test setup/teardown
- Function pointers for test registration

## Features
- Test suite organization
- Assertions (ASSERT_EQ, ASSERT_TRUE, ASSERT_THROW, etc.)
- Test fixtures with setup/teardown
- Test discovery and automatic registration
- Colorized output
- Test filtering

## C++ Features Tested
1. **Macros**: Test definition and assertion macros
2. **Templates**: Generic test fixtures
3. **Exceptions**: Assertion failures
4. **RAII**: Fixture setup/teardown
5. **Function Pointers**: Test registration
6. **STL**: std::vector, std::string, std::function

## Target Size
1,500-2,500 LOC
