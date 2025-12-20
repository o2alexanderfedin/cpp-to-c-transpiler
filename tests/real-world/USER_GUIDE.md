# Real-World Testing - User Guide

Complete user guide for working with the real-world testing suite.

## Introduction

This guide helps you understand, use, and contribute to the real-world testing infrastructure for the C++ to C transpiler.

## What is Real-World Testing?

Real-world testing validates the transpiler using actual production-quality C++ code, not just synthetic test cases. This ensures:

✓ **Real Patterns**: Code uses actual design patterns and idioms  
✓ **Complex Features**: Projects combine multiple C++ features  
✓ **Edge Cases**: Real code reveals corner cases synthetic tests miss  
✓ **Integration**: Features work together correctly  
✓ **Performance**: Real workloads validate performance  

## The 5 Test Projects

### JSON Parser
A complete JSON parser demonstrating parsing, recursion, and data structures.

**Use Cases:**
- Configuration file parsing
- API response handling
- Data serialization/deserialization

**Learn About:**
- Recursive descent parsing
- Exception handling for errors
- Polymorphic type hierarchies
- Smart pointer usage

### Logger  
A multi-level logging system with console and file outputs.

**Use Cases:**
- Application logging
- Error tracking
- Debug output
- Audit trails

**Learn About:**
- RAII for resource management
- Multiple inheritance
- Template-based formatting
- Stream operators

### Test Framework
A minimal unit testing framework with assertions and fixtures.

**Use Cases:**
- Unit testing
- Integration testing
- Test automation

**Learn About:**
- Test organization
- Assertion mechanisms
- Exception-based failures
- Fixture setup/teardown

### String Formatter
Type-safe string formatting with custom specifiers.

**Use Cases:**
- Formatted output
- Report generation
- String manipulation

**Learn About:**
- Variadic templates
- Template specialization
- Type traits
- Operator overloading

### Resource Manager
Generic resource management with RAII and pooling.

**Use Cases:**
- Memory management
- File handle management
- Connection pooling
- Object lifecycle

**Learn About:**
- RAII patterns
- Move semantics
- Reference counting
- Resource pooling

## Getting Started

### Prerequisites

You need:
1. C++17 compiler (g++ 7+ or clang++ 5+)
2. CMake 3.20+
3. Git (for cloning)
4. cpptoc transpiler (from main project)

### Installation

```bash
# Clone repository
git clone https://github.com/yourusername/cpp-to-c-transpiler.git
cd cpp-to-c-transpiler

# Build main project
mkdir build
cd build
cmake ..
make

# Navigate to real-world tests
cd ../tests/real-world
```

### Quick Test

```bash
# Build all projects
for dir in json-parser logger test-framework string-formatter resource-manager; do
    cd $dir
    mkdir -p build
    cd build
    cmake ..
    make
    cd ../..
done

# Run all tests
for dir in */build; do
    cd $dir
    ctest
    cd ../..
done
```

## Working with JSON Parser

### Basic Usage

```cpp
#include "JsonParser.h"
#include "JsonValue.h"

using namespace json;

int main() {
    // Parse JSON string
    JsonParser parser;
    std::string json = R"({"name": "Alice", "age": 30})";
    
    auto root = parser.parse(json);
    
    // Access values
    if (root->isObject()) {
        const auto& obj = root->asObject();
        std::cout << "Name: " << obj["name"].asString() << std::endl;
        std::cout << "Age: " << obj["age"].asNumber() << std::endl;
    }
    
    return 0;
}
```

### Building JSON Programmatically

```cpp
// Create object
auto obj = std::make_unique<JsonObject>();
obj->insert("name", std::make_unique<JsonString>("Bob"));
obj->insert("age", std::make_unique<JsonNumber>(25));

// Create array
auto arr = std::make_unique<JsonArray>();
arr->push(std::make_unique<JsonNumber>(1));
arr->push(std::make_unique<JsonNumber>(2));
arr->push(std::make_unique<JsonNumber>(3));

obj->insert("scores", std::move(arr));

// Output
std::cout << obj->toString() << std::endl;
```

### Error Handling

```cpp
try {
    auto value = parser.parse(invalidJson);
} catch (const ParseError& e) {
    std::cerr << "Parse error: " << e.what() << std::endl;
    std::cerr << "File: " << e.getFile() << std::endl;
    std::cerr << "Line: " << e.getLine() << std::endl;
}
```

## Working with Logger

### Console Logging

```cpp
#include "Logger.h"

using namespace logging;

int main() {
    ConsoleLogger logger("MyApp", LogLevel::INFO);
    
    logger.info("Application started");
    logger.warn("Low memory");
    logger.error("Connection failed");
    
    return 0;
}
```

### File Logging

```cpp
// Log to file
FileLogger logger("MyApp", "app.log", LogLevel::DEBUG);

logger.debug("Debug information");
logger.info("Processing request");
logger.error("Error occurred");

// File automatically closed when logger destroyed
```

### Multi-Target Logging

```cpp
MultiLogger multi("MyApp", LogLevel::DEBUG);

// Console for warnings and above
multi.addLogger(std::make_unique<ConsoleLogger>("Console", LogLevel::WARN));

// File for all levels
multi.addLogger(std::make_unique<FileLogger>("File", "debug.log", LogLevel::DEBUG));

// Errors to separate file
multi.addLogger(std::make_unique<FileLogger>("Errors", "errors.log", LogLevel::ERROR));

multi.debug("Debug (file only)");
multi.info("Info (file only)");
multi.warn("Warning (console + files)");
multi.error("Error (all destinations)");
```

### Stream-Style Logging

```cpp
ConsoleLogger logger("MyApp", LogLevel::INFO);

info(logger) << "User " << userId << " logged in";
warn(logger) << "Cache at " << cachePercent << "% capacity";
error(logger) << "Failed after " << retries << " attempts";
```

## Working with Test Framework

### Writing Tests

```cpp
#include "TestFramework.h"

using namespace test;

class MyTest : public TestCase {
public:
    MyTest() : TestCase("MyTest") {}
    
    void run() override {
        // Test code
        int result = 2 + 2;
        ASSERT_EQ(result, 4);
    }
};
```

### Using Fixtures

```cpp
class DatabaseFixture : public TestCase {
protected:
    Database* db;
    
    void setUp() override {
        db = new Database();
        db->connect();
    }
    
    void tearDown() override {
        db->disconnect();
        delete db;
    }
    
public:
    DatabaseFixture(const std::string& name) : TestCase(name) {}
};

class DatabaseQueryTest : public DatabaseFixture {
public:
    DatabaseQueryTest() : DatabaseFixture("DatabaseQuery") {}
    
    void run() override {
        auto result = db->query("SELECT * FROM users");
        ASSERT_TRUE(result.size() > 0);
    }
};
```

### Running Tests

```cpp
int main() {
    auto suite = std::make_unique<TestSuite>("DatabaseTests");
    
    suite->addTest(std::make_unique<DatabaseQueryTest>());
    suite->addTest(std::make_unique<DatabaseInsertTest>());
    
    TestRegistry::getInstance().addSuite("DatabaseTests", std::move(suite));
    
    return RUN_ALL_TESTS();
}
```

## Working with String Formatter

### Basic Formatting

```cpp
#include "StringFormatter.h"

using namespace format;

int main() {
    // Simple formatting
    std::string s1 = formatString("Hello, {}!", "World");
    
    // Multiple arguments
    std::string s2 = formatString("{} + {} = {}", 2, 2, 4);
    
    // Indexed arguments
    std::string s3 = formatString("{1} {0}", "World", "Hello");
    
    return 0;
}
```

### Format Specifications

```cpp
FormatSpec spec;
spec.align = Align::Right;
spec.width = 10;
spec.precision = 2;

std::string formatted = toString(3.14159, spec);
// "      3.14"
```

### Number Formatting

```cpp
int num = 255;

std::string hex = formatters::hex(num);         // "0xff"
std::string oct = formatters::oct(num);         // "0o377"
std::string bin = formatters::bin(num);         // "0b11111111"

double pi = 3.14159;
std::string fixed = formatters::fixed(pi, 2);   // "3.14"
std::string sci = formatters::scientific(pi);    // "3.14e+00"
```

### Stream Building

```cpp
StringBuilder sb;
sb << "Name: " << name;
sb << ", Age: " << age;
sb << ", Score: " << score;

std::cout << sb.str() << std::endl;
```

## Working with Resource Manager

### Basic Resource Handles

```cpp
#include "ResourceManager.h"

using namespace resman;

int main() {
    // Unique ownership
    ResourceHandle<MyResource> handle(new MyResource());
    handle->doSomething();
    
    // Automatically deleted when handle destroyed
    return 0;
}
```

### Shared Resources

```cpp
// Reference-counted resource
SharedResource<Data> shared1(new Data());
SharedResource<Data> shared2 = shared1;  // Share ownership

std::cout << shared1.useCount(); // 2

shared2.reset(); // Release one reference
std::cout << shared1.useCount(); // 1

// Resource deleted when last reference destroyed
```

### Scope Guards

```cpp
FILE* file = fopen("data.txt", "w");
auto guard = makeScopeGuard([file]() {
    if (file) fclose(file);
});

// Use file...
fprintf(file, "Hello\n");

// File automatically closed when guard destroyed
```

### Memory Pools

```cpp
MemoryPool<MyObject> pool(100);

// Allocate from pool
MyObject* obj = pool.allocate();
obj->setValue(42);

// Use object...

// Return to pool
pool.deallocate(obj);
```

### Resource Pools with RAII

```cpp
ResourcePool<Connection> pool(10);

// Add connections to pool
for (int i = 0; i < 10; ++i) {
    pool.add(std::make_unique<Connection>());
}

// Use pooled resource with RAII
{
    PooledResource<Connection> conn(pool);
    conn->send("data");
    conn->receive();
} // Automatically returned to pool
```

### File Resources

```cpp
// RAII file handling
FileResource file("data.txt", "w");
file.write("Line 1\n");
file.write("Line 2\n");
// File automatically closed
```

## Best Practices

### Error Handling

Always handle potential errors:

```cpp
try {
    auto value = parser.parse(userInput);
    processValue(value);
} catch (const ParseError& e) {
    logger.error("Parse error: " + std::string(e.what()));
    return false;
} catch (const std::exception& e) {
    logger.error("Unexpected error: " + std::string(e.what()));
    return false;
}
```

### Resource Management

Use RAII consistently:

```cpp
// Good - automatic cleanup
{
    FileResource file("data.txt", "w");
    file.write("data");
} // File closed here

// Bad - manual cleanup prone to errors
FILE* file = fopen("data.txt", "w");
fprintf(file, "data");
fclose(file); // Easy to forget or skip on error
```

### Logging

Log at appropriate levels:

```cpp
logger.debug("Entering function with param=" + std::to_string(param));
logger.info("Processing started");
logger.warn("Using fallback configuration");
logger.error("Operation failed: " + error);
logger.fatal("Critical system failure");
```

### Testing

Write comprehensive tests:

```cpp
// Test normal case
ASSERT_EQ(add(2, 2), 4);

// Test edge cases
ASSERT_EQ(add(0, 0), 0);
ASSERT_EQ(add(-1, 1), 0);

// Test error cases
ASSERT_THROW(divide(1, 0));
```

## Troubleshooting

### Common Build Issues

**Issue**: CMake can't find compiler
```
Solution: export CXX=g++ or cmake -DCMAKE_CXX_COMPILER=g++ ..
```

**Issue**: Header not found
```
Solution: Check include_directories() in CMakeLists.txt
```

**Issue**: Linking errors
```
Solution: Check target_link_libraries() in CMakeLists.txt
```

### Common Runtime Issues

**Issue**: Segmentation fault
```
Solution: Run with valgrind or AddressSanitizer
valgrind --leak-check=full ./test_program
```

**Issue**: Memory leak
```
Solution: Check resource cleanup, use RAII
```

**Issue**: Assertion failure
```
Solution: Check test logic, add debug output
```

### Performance Issues

**Issue**: Slow execution
```
Solution: Profile with gprof or perf
cmake -DCMAKE_CXX_FLAGS="-pg" ..
make
./test_program
gprof test_program gmon.out > profile.txt
```

## Advanced Usage

### Custom JSON Types

```cpp
class MyType {
    std::string data;
public:
    explicit MyType(const std::string& d) : data(d) {}
    
    std::unique_ptr<JsonValue> toJSON() const {
        auto obj = std::make_unique<JsonObject>();
        obj->insert("data", std::make_unique<JsonString>(data));
        return obj;
    }
};
```

### Custom Loggers

```cpp
class DatabaseLogger : public Logger {
    Database& db;
public:
    DatabaseLogger(Database& database) 
        : Logger("DB", LogLevel::INFO), db(database) {}
    
    void write(LogLevel level, const std::string& message) override {
        db.execute("INSERT INTO logs (level, message) VALUES (?, ?)",
                   levelToString(level), message);
    }
};
```

### Custom Formatters

```cpp
template<>
struct Formatter<MyType> {
    static std::string format(const MyType& value, const FormatSpec& spec) {
        return "MyType(" + value.toString() + ")";
    }
};
```

### Custom Deleters

```cpp
struct NetworkDeleter {
    void operator()(Connection* conn) const {
        if (conn) {
            conn->disconnect();
            delete conn;
        }
    }
};

using NetworkHandle = ResourceHandle<Connection, NetworkDeleter>;
```

## Integration Examples

### Complete Application Example

```cpp
#include "JsonParser.h"
#include "Logger.h"
#include "ResourceManager.h"

using namespace json;
using namespace logging;
using namespace resman;

class Application {
    MultiLogger logger_;
    ResourcePool<Connection> connPool_;
    
public:
    Application() : logger_("App", LogLevel::INFO), connPool_(10) {
        // Setup logging
        logger_.addLogger(std::make_unique<ConsoleLogger>("Console", LogLevel::INFO));
        logger_.addLogger(std::make_unique<FileLogger>("File", "app.log", LogLevel::DEBUG));
        
        // Initialize connection pool
        for (int i = 0; i < 10; ++i) {
            connPool_.add(std::make_unique<Connection>());
        }
    }
    
    void processRequest(const std::string& jsonRequest) {
        logger_.info("Processing request");
        
        try {
            // Parse JSON
            JsonParser parser;
            auto request = parser.parse(jsonRequest);
            
            // Get connection from pool
            PooledResource<Connection> conn(connPool_);
            
            // Process request
            const auto& data = request->asObject();
            std::string result = conn->query(data["query"].asString());
            
            logger_.info("Request processed successfully");
            
        } catch (const ParseError& e) {
            logger_.error("Invalid JSON: " + std::string(e.what()));
        } catch (const ResourceError& e) {
            logger_.error("Resource error: " + std::string(e.what()));
        }
    }
};
```

### Test Suite Example

```cpp
#include "TestFramework.h"
#include "JsonParser.h"

using namespace test;
using namespace json;

class JsonParserTestSuite {
public:
    static void registerTests() {
        auto suite = std::make_unique<TestSuite>("JsonParser");
        
        suite->addTest(std::make_unique<ParseNullTest>());
        suite->addTest(std::make_unique<ParseBoolTest>());
        suite->addTest(std::make_unique<ParseNumberTest>());
        suite->addTest(std::make_unique<ParseStringTest>());
        suite->addTest(std::make_unique<ParseArrayTest>());
        suite->addTest(std::make_unique<ParseObjectTest>());
        
        TestRegistry::getInstance().addSuite("JsonParser", std::move(suite));
    }
};

int main() {
    JsonParserTestSuite::registerTests();
    return RUN_ALL_TESTS();
}
```

## Performance Tips

### JSON Parsing
- Pre-allocate containers when size known
- Use move semantics for large strings
- Reuse parser objects

### Logging
- Use appropriate log levels
- Avoid logging in tight loops
- Use stream-style for complex messages
- Consider async logging for high-volume

### String Formatting
- Reuse StringBuilder objects
- Pre-allocate when size known
- Use formatString for simple cases

### Resource Management
- Use resource pools for frequently allocated objects
- Prefer stack allocation when possible
- Use move semantics to avoid copies
- Profile before optimizing

## Conclusion

This guide covered:
- ✓ Understanding real-world testing
- ✓ Working with each test project
- ✓ Best practices
- ✓ Troubleshooting
- ✓ Advanced usage
- ✓ Integration examples

For more information:
- API Documentation: API_DOCUMENTATION.md
- Implementation Guide: IMPLEMENTATION_GUIDE.md
- Testing Report: TESTING_REPORT.md
- Project README: README.md

---

**Version**: 1.0
**Last Updated**: 2025-12-18
**Status**: Complete
