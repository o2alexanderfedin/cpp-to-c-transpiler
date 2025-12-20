# Real-World Projects - API Documentation

Complete API reference for all 5 real-world test projects.

## Table of Contents

1. [JSON Parser API](#json-parser-api)
2. [Logger API](#logger-api)
3. [Test Framework API](#test-framework-api)
4. [String Formatter API](#string-formatter-api)
5. [Resource Manager API](#resource-manager-api)

---

## JSON Parser API

### Namespace: `json`

### Classes

#### `JsonValue` (Abstract Base Class)

Base class for all JSON value types.

**Public Methods:**

```cpp
virtual Type getType() const = 0;
```
Returns the type of this JSON value.

```cpp
virtual std::string toString() const = 0;
```
Converts this value to a JSON string representation.

```cpp
virtual std::unique_ptr<JsonValue> clone() const = 0;
```
Creates a deep copy of this value.

```cpp
bool isNull() const;
bool isBool() const;
bool isNumber() const;
bool isString() const;
bool isArray() const;
bool isObject() const;
```
Type checking methods.

```cpp
bool asBool() const;
double asNumber() const;
const std::string& asString() const;
const JsonArray& asArray() const;
const JsonObject& asObject() const;
JsonArray& asArray();
JsonObject& asObject();
```
Type conversion methods. Throw `std::runtime_error` if type mismatch.

**Example:**
```cpp
JsonParser parser;
auto value = parser.parse("{\"key\": 42}");

if (value->isObject()) {
    const auto& obj = value->asObject();
    double num = obj["key"].asNumber();
}
```

#### `JsonNull`

Represents JSON null value.

**Methods:**
- `Type getType() const override` - Returns `Type::Null`
- `std::string toString() const override` - Returns `"null"`

**Example:**
```cpp
auto nullValue = std::make_unique<JsonNull>();
std::cout << nullValue->toString(); // "null"
```

#### `JsonBool`

Represents JSON boolean value.

**Constructor:**
```cpp
explicit JsonBool(bool value);
```

**Methods:**
- `bool getValue() const` - Returns the boolean value
- `Type getType() const override` - Returns `Type::Bool`
- `std::string toString() const override` - Returns `"true"` or `"false"`

**Example:**
```cpp
auto trueValue = std::make_unique<JsonBool>(true);
std::cout << trueValue->getValue(); // true
```

#### `JsonNumber`

Represents JSON number value.

**Constructor:**
```cpp
explicit JsonNumber(double value);
```

**Methods:**
- `double getValue() const` - Returns the numeric value
- `Type getType() const override` - Returns `Type::Number`
- `std::string toString() const override` - Returns string representation

**Example:**
```cpp
auto number = std::make_unique<JsonNumber>(3.14);
std::cout << number->getValue(); // 3.14
```

#### `JsonString`

Represents JSON string value.

**Constructors:**
```cpp
explicit JsonString(const std::string& value);
explicit JsonString(std::string&& value);  // Move constructor
```

**Methods:**
- `const std::string& getValue() const` - Returns the string value
- `Type getType() const override` - Returns `Type::String`
- `std::string toString() const override` - Returns quoted, escaped string

**Example:**
```cpp
auto str = std::make_unique<JsonString>("Hello, World!");
std::cout << str->toString(); // "\"Hello, World!\""
```

#### `JsonArray`

Represents JSON array value.

**Methods:**
```cpp
void push(std::unique_ptr<JsonValue> value);
```
Adds a value to the end of the array.

```cpp
size_t size() const;
bool empty() const;
```
Size and empty checks.

```cpp
const JsonValue& operator[](size_t index) const;
JsonValue& operator[](size_t index);
```
Index access. Throws `std::out_of_range` if index invalid.

**Example:**
```cpp
auto arr = std::make_unique<JsonArray>();
arr->push(std::make_unique<JsonNumber>(1));
arr->push(std::make_unique<JsonNumber>(2));
arr->push(std::make_unique<JsonNumber>(3));

std::cout << (*arr)[0].asNumber(); // 1.0
```

#### `JsonObject`

Represents JSON object value.

**Methods:**
```cpp
void insert(const std::string& key, std::unique_ptr<JsonValue> value);
```
Inserts a key-value pair.

```cpp
bool contains(const std::string& key) const;
```
Checks if key exists.

```cpp
size_t size() const;
bool empty() const;
```
Size and empty checks.

```cpp
const JsonValue& operator[](const std::string& key) const;
JsonValue& operator[](const std::string& key);
```
Key access. Throws `std::out_of_range` if key not found.

**Iterators:**
```cpp
const_iterator begin() const;
const_iterator end() const;
```
Iterate over key-value pairs.

**Example:**
```cpp
auto obj = std::make_unique<JsonObject>();
obj->insert("name", std::make_unique<JsonString>("Alice"));
obj->insert("age", std::make_unique<JsonNumber>(30));

if (obj->contains("name")) {
    std::cout << obj->operator[]("name").asString();
}

for (const auto& pair : *obj) {
    std::cout << pair.first << ": " << pair.second->toString() << std::endl;
}
```

#### `JsonParser`

Parses JSON strings into `JsonValue` objects.

**Methods:**
```cpp
std::unique_ptr<JsonValue> parse(const std::string& json);
```
Parses a JSON string. Throws `ParseError` on invalid JSON.

**Example:**
```cpp
JsonParser parser;
try {
    auto value = parser.parse("{\"key\": \"value\"}");
    // Use value...
} catch (const ParseError& e) {
    std::cerr << "Parse error: " << e.what() << std::endl;
}
```

#### `ParseError`

Exception thrown on JSON parse errors.

**Inherits:** `std::runtime_error`

**Constructors:**
```cpp
explicit ParseError(const std::string& message);
ParseError(const std::string& message, size_t line, size_t column);
```

**Example:**
```cpp
try {
    parser.parse("invalid json");
} catch (const ParseError& e) {
    std::cout << "Error: " << e.what() << std::endl;
}
```

---

## Logger API

### Namespace: `logging`

### Enums

#### `LogLevel`

```cpp
enum class LogLevel {
    DEBUG = 0,
    INFO = 1,
    WARN = 2,
    ERROR = 3,
    FATAL = 4
};
```

### Classes

#### `Logger` (Abstract Base Class)

**Constructor:**
```cpp
explicit Logger(const std::string& name, LogLevel minLevel = LogLevel::INFO);
```

**Public Methods:**
```cpp
virtual void write(LogLevel level, const std::string& message) = 0;
```
Pure virtual method for writing log messages.

```cpp
void debug(const std::string& message);
void info(const std::string& message);
void warn(const std::string& message);
void error(const std::string& message);
void fatal(const std::string& message);
```
Convenience methods for different log levels.

```cpp
template<typename T>
void log(LogLevel level, const T& message);
```
Generic logging method.

```cpp
void setLevel(LogLevel level);
LogLevel getLevel() const;
const std::string& getName() const;
```
Getters and setters.

**Example:**
```cpp
class MyLogger : public Logger {
public:
    MyLogger(const std::string& name) : Logger(name, LogLevel::INFO) {}
    
    void write(LogLevel level, const std::string& message) override {
        // Custom implementation
    }
};
```

#### `ConsoleLogger`

Logs to console (stdout/stderr).

**Constructor:**
```cpp
explicit ConsoleLogger(const std::string& name,
                      LogLevel minLevel = LogLevel::INFO,
                      bool useStderr = false);
```

**Parameters:**
- `name` - Logger name
- `minLevel` - Minimum log level to output
- `useStderr` - Use stderr instead of stdout

**Example:**
```cpp
ConsoleLogger logger("App", LogLevel::DEBUG);
logger.debug("Debug message");
logger.info("Info message");
logger.error("Error message");
```

#### `FileLogger`

Logs to file with RAII.

**Constructor:**
```cpp
explicit FileLogger(const std::string& name,
                   const std::string& filename,
                   LogLevel minLevel = LogLevel::INFO,
                   bool append = true);
```

**Parameters:**
- `name` - Logger name
- `filename` - Output file path
- `minLevel` - Minimum log level
- `append` - Append to existing file (true) or truncate (false)

**Methods:**
```cpp
const std::string& getFilename() const;
```
Returns the log file path.

**Example:**
```cpp
FileLogger logger("App", "app.log", LogLevel::INFO, true);
logger.info("Application started");
logger.warn("Low memory");
logger.error("Connection failed");
// File automatically closed when logger goes out of scope
```

#### `MultiLogger`

Logs to multiple destinations simultaneously.

**Constructor:**
```cpp
explicit MultiLogger(const std::string& name, LogLevel minLevel = LogLevel::INFO);
```

**Methods:**
```cpp
void addLogger(std::unique_ptr<Logger> logger);
```
Adds a logger to the collection.

```cpp
size_t count() const;
```
Returns number of loggers.

**Example:**
```cpp
MultiLogger multi("App", LogLevel::DEBUG);
multi.addLogger(std::make_unique<ConsoleLogger>("Console", LogLevel::INFO));
multi.addLogger(std::make_unique<FileLogger>("File", "app.log", LogLevel::DEBUG));
multi.addLogger(std::make_unique<FileLogger>("Errors", "errors.log", LogLevel::ERROR));

multi.debug("Debug (file only)");
multi.info("Info (console + file)");
multi.error("Error (all destinations)");
```

#### `LogStream`

Stream-style logging helper.

**Constructor:**
```cpp
LogStream(Logger& logger, LogLevel level);
```

**Operators:**
```cpp
template<typename T>
LogStream& operator<<(const T& value);
```

**Example:**
```cpp
ConsoleLogger logger("App", LogLevel::INFO);
info(logger) << "User " << "alice" << " logged in at " << 1234567890;
```

### Free Functions

```cpp
LogStream debug(Logger& logger);
LogStream info(Logger& logger);
LogStream warn(Logger& logger);
LogStream error(Logger& logger);
LogStream fatal(Logger& logger);
```

Create `LogStream` for different levels.

**Example:**
```cpp
debug(logger) << "x = " << x << ", y = " << y;
```

---

## Test Framework API

### Namespace: `test`

### Classes

#### `TestFailure`

Exception thrown when assertion fails.

**Inherits:** `std::runtime_error`

**Constructor:**
```cpp
TestFailure(const std::string& message, const std::string& file, int line);
```

**Methods:**
```cpp
const std::string& getFile() const;
int getLine() const;
std::string fullMessage() const;
```

**Example:**
```cpp
throw TestFailure("Expected 5, got 3", __FILE__, __LINE__);
```

#### `TestCase` (Abstract Base Class)

**Constructor:**
```cpp
explicit TestCase(const std::string& name);
```

**Protected Virtual Methods:**
```cpp
virtual void setUp();
virtual void tearDown();
```
Setup and cleanup hooks.

**Public Pure Virtual:**
```cpp
virtual void run() = 0;
```
Test implementation.

**Methods:**
```cpp
const std::string& getName() const;
TestResult execute();
```

**Example:**
```cpp
class MyTest : public TestCase {
public:
    MyTest() : TestCase("MyTest") {}
    
    void setUp() override {
        // Setup code
    }
    
    void run() override {
        ASSERT_EQ(2 + 2, 4);
    }
    
    void tearDown() override {
        // Cleanup code
    }
};
```

#### `TestSuite`

Collection of tests.

**Constructor:**
```cpp
explicit TestSuite(const std::string& name);
```

**Methods:**
```cpp
void addTest(std::unique_ptr<TestCase> test);
std::vector<TestResult> run();
const std::string& getName() const;
size_t size() const;
```

**Example:**
```cpp
auto suite = std::make_unique<TestSuite>("MathTests");
suite->addTest(std::make_unique<AdditionTest>());
suite->addTest(std::make_unique<SubtractionTest>());
auto results = suite->run();
```

#### `TestRegistry`

Singleton registry for test suites.

**Methods:**
```cpp
static TestRegistry& getInstance();
void addSuite(const std::string& name, std::unique_ptr<TestSuite> suite);
TestSuite* getSuite(const std::string& name);
std::vector<std::string> getSuiteNames() const;
int runAll();
```

**Example:**
```cpp
TestRegistry::getInstance().addSuite("MathTests", std::move(suite));
int result = TestRegistry::getInstance().runAll();
```

### Assertion Functions

#### Boolean Assertions
```cpp
void assertTrue(bool condition, const std::string& message,
               const std::string& file, int line);
void assertFalse(bool condition, const std::string& message,
                const std::string& file, int line);
```

#### Comparison Assertions
```cpp
template<typename T1, typename T2>
void assertEqual(const T1& actual, const T2& expected,
                const std::string& file, int line);

template<typename T1, typename T2>
void assertNotEqual(const T1& actual, const T2& expected,
                   const std::string& file, int line);

template<typename T1, typename T2>
void assertLess(const T1& actual, const T2& limit,
               const std::string& file, int line);

template<typename T1, typename T2>
void assertGreater(const T1& actual, const T2& limit,
                  const std::string& file, int line);
```

#### Pointer Assertions
```cpp
void assertNull(const void* ptr, const std::string& file, int line);
void assertNotNull(const void* ptr, const std::string& file, int line);
```

#### Exception Assertions
```cpp
template<typename Func>
void assertThrows(Func func, const std::string& file, int line);

template<typename Exception, typename Func>
void assertThrowsType(Func func, const std::string& file, int line);
```

### Assertion Macros

```cpp
ASSERT_TRUE(condition)
ASSERT_FALSE(condition)
ASSERT_EQ(actual, expected)
ASSERT_NE(actual, expected)
ASSERT_LT(actual, limit)
ASSERT_GT(actual, limit)
ASSERT_NULL(ptr)
ASSERT_NOT_NULL(ptr)
ASSERT_THROW(expression)
ASSERT_THROW_TYPE(expression, exception_type)
```

**Example:**
```cpp
ASSERT_TRUE(result);
ASSERT_EQ(actual, 42);
ASSERT_NULL(ptr);
ASSERT_THROW(riskyOperation());
ASSERT_THROW_TYPE(divide(1, 0), std::invalid_argument);
```

### Test Definition Macros

```cpp
TEST_CASE(suite, name) { /* test code */ }
RUN_ALL_TESTS()
```

**Example:**
```cpp
TEST_CASE(MathTests, Addition) {
    ASSERT_EQ(2 + 2, 4);
}

int main() {
    return RUN_ALL_TESTS();
}
```

---

## String Formatter API

### Namespace: `format`

### Enums

#### `Align`
```cpp
enum class Align {
    Left,
    Right,
    Center
};
```

#### `Base`
```cpp
enum class Base {
    Decimal = 10,
    Hexadecimal = 16,
    Octal = 8,
    Binary = 2
};
```

### Structs

#### `FormatSpec`

Format specification for values.

**Fields:**
```cpp
Align align;        // Alignment (default: Left)
int width;          // Minimum width (default: 0)
int precision;      // Decimal precision (default: 6)
char fill;          // Fill character (default: ' ')
Base base;          // Number base (default: Decimal)
bool showBase;      // Show base prefix (default: false)
bool showPos;       // Show + for positive (default: false)
bool upperCase;     // Uppercase output (default: false)
bool scientific;    // Scientific notation (default: false)
```

**Example:**
```cpp
FormatSpec spec;
spec.align = Align::Right;
spec.width = 10;
spec.fill = '0';
std::string result = toString(42, spec); // "0000000042"
```

### Templates

#### `Formatter<T>`

Type-specific formatter.

**Static Method:**
```cpp
static std::string format(const T& value, const FormatSpec& spec);
```

**Specializations:**
- `Formatter<T>` (integral types)
- `Formatter<T>` (floating-point types)
- `Formatter<bool>`
- `Formatter<const char*>`
- `Formatter<std::string>`
- `Formatter<T*>` (pointers)

**Example:**
```cpp
// Custom formatter
template<>
struct Formatter<MyType> {
    static std::string format(const MyType& value, const FormatSpec& spec) {
        // Custom formatting logic
    }
};
```

### Classes

#### `StringBuilder`

Build strings incrementally.

**Methods:**
```cpp
StringBuilder& append(const std::string& str);

template<typename T>
StringBuilder& append(const T& value, const FormatSpec& spec = FormatSpec());

template<typename T>
StringBuilder& operator<<(const T& value);

std::string str() const;
void clear();
bool empty() const;
size_t length() const;
```

**Example:**
```cpp
StringBuilder sb;
sb << "Hello, " << "World" << "!";
sb.append(" Value: ").append(42);
std::cout << sb.str(); // "Hello, World! Value: 42"
```

#### `FormatStream`

Stream-style formatting.

**Operators:**
```cpp
template<typename T>
FormatStream& operator<<(const T& value);
```

**Methods:**
```cpp
std::string str() const;
operator std::string() const;
```

**Example:**
```cpp
FormatStream fs;
fs << "Result: " << 42 << ", " << 3.14;
std::string result = fs; // Implicit conversion
```

### Free Functions

#### `formatString`

Printf-style formatting with placeholders.

```cpp
template<typename... Args>
std::string formatString(const std::string& fmt, Args&&... args);
```

**Placeholder Syntax:**
- `{}` - Automatic argument index
- `{0}`, `{1}`, ... - Explicit argument index
- `{:spec}` - Format specification
- `{{` - Escaped brace
- `}}` - Escaped brace

**Example:**
```cpp
std::string result = formatString("Hello, {}!", "World");
// "Hello, World!"

std::string indexed = formatString("{1} {0}", "World", "Hello");
// "Hello World"

std::string formatted = formatString("Value: {:.2f}", 3.14159);
// "Value: 3.14"
```

#### `toString`

Convert value to string.

```cpp
template<typename T>
std::string toString(const T& value);

template<typename T>
std::string toString(const T& value, const FormatSpec& spec);
```

**Example:**
```cpp
std::string s1 = toString(42);
std::string s2 = toString(3.14159, spec);
```

#### Helper Functions

```cpp
FormatSpec spec(Align align = Align::Left, int width = 0, int precision = 6);
```

**Example:**
```cpp
auto s = spec(Align::Right, 10, 2);
```

### Formatters Namespace

#### Number Formatters

```cpp
template<typename T>
std::string hex(const T& value, bool uppercase = false, bool showBase = true);

template<typename T>
std::string oct(const T& value, bool showBase = true);

template<typename T>
std::string bin(const T& value, bool showBase = true);

template<typename T>
std::string scientific(const T& value, int precision = 6, bool uppercase = false);

template<typename T>
std::string fixed(const T& value, int precision = 2);
```

**Example:**
```cpp
std::string hexStr = formatters::hex(255);        // "0xff"
std::string octStr = formatters::oct(64);         // "0o100"
std::string binStr = formatters::bin(5);          // "0b101"
std::string sciStr = formatters::scientific(12345.6, 2); // "1.23e+04"
std::string fixStr = formatters::fixed(3.14159, 2);     // "3.14"
```

#### String Formatters

```cpp
std::string pad(const std::string& str, int width,
               Align align = Align::Left, char fill = ' ');
```

**Example:**
```cpp
std::string padded = formatters::pad("test", 10, Align::Center, '-');
// "---test---"
```

---

## Resource Manager API

### Namespace: `resman`

### Exceptions

#### `ResourceError`

**Inherits:** `std::runtime_error`

**Constructor:**
```cpp
explicit ResourceError(const std::string& message);
```

### Templates

#### `ResourceHandle<T, Deleter>`

Unique ownership resource handle (similar to unique_ptr).

**Type Parameters:**
- `T` - Resource type
- `Deleter` - Deleter type (default: `std::default_delete<T>`)

**Constructors:**
```cpp
explicit ResourceHandle(T* resource = nullptr, Deleter deleter = Deleter());
ResourceHandle(ResourceHandle&& other) noexcept;  // Move
```

**Deleted:**
```cpp
ResourceHandle(const ResourceHandle&) = delete;  // No copy
ResourceHandle& operator=(const ResourceHandle&) = delete;
```

**Methods:**
```cpp
void reset(T* newResource = nullptr);
T* release();
T* get() const;
T& operator*() const;
T* operator->() const;
explicit operator bool() const;
void swap(ResourceHandle& other) noexcept;
```

**Example:**
```cpp
ResourceHandle<int> handle(new int(42));
std::cout << *handle; // 42
int* raw = handle.release(); // Take ownership
delete raw;
```

#### `SharedResource<T, Deleter>`

Reference-counted resource (similar to shared_ptr).

**Constructors:**
```cpp
explicit SharedResource(T* resource = nullptr, Deleter deleter = Deleter());
SharedResource(const SharedResource& other);      // Copy
SharedResource(SharedResource&& other) noexcept;  // Move
```

**Methods:**
```cpp
void reset(T* newResource = nullptr);
T* get() const;
T& operator*() const;
T* operator->() const;
explicit operator bool() const;
int useCount() const;
```

**Example:**
```cpp
SharedResource<int> shared1(new int(42));
SharedResource<int> shared2 = shared1;  // Reference count: 2
std::cout << shared1.useCount(); // 2
```

#### `ScopeGuard<Func>`

RAII cleanup on scope exit.

**Constructor:**
```cpp
explicit ScopeGuard(Func func);
```

**Methods:**
```cpp
void dismiss();
```

**Example:**
```cpp
FILE* file = fopen("test.txt", "w");
auto guard = makeScopeGuard([file]() {
    if (file) fclose(file);
});

// Use file...

guard.dismiss(); // Cancel cleanup
fclose(file);    // Manual cleanup instead
```

#### `MemoryPool<T>`

Fixed-size object pool.

**Constructor:**
```cpp
explicit MemoryPool(size_t capacity = 100);
```

**Methods:**
```cpp
T* allocate();
void deallocate(T* ptr);
size_t capacity() const;
size_t used() const;
size_t available() const;
```

**Example:**
```cpp
MemoryPool<int> pool(100);
int* obj1 = pool.allocate();
*obj1 = 42;
pool.deallocate(obj1);
```

#### `ResourcePool<T>`

Generic resource pooling.

**Constructor:**
```cpp
explicit ResourcePool(size_t capacity);
```

**Methods:**
```cpp
void add(std::unique_ptr<T> resource);
T* acquire();
void release(T* resource);
size_t capacity() const;
size_t available() const;
size_t inUse() const;
```

**Example:**
```cpp
ResourcePool<Connection> pool(10);
pool.add(std::make_unique<Connection>());

Connection* conn = pool.acquire();
// Use connection...
pool.release(conn);
```

#### `PooledResource<T>`

RAII wrapper for pooled resources.

**Constructor:**
```cpp
PooledResource(ResourcePool<T>& pool);
```

**Methods:**
```cpp
T* get() const;
T& operator*() const;
T* operator->() const;
```

**Example:**
```cpp
ResourcePool<Connection> pool(10);
pool.add(std::make_unique<Connection>());

{
    PooledResource<Connection> conn(pool);
    conn->send("data");
} // Automatically released back to pool
```

### Type Aliases

```cpp
using FileHandle = ResourceHandle<std::FILE, FileDeleter>;
using MemoryHandle = ResourceHandle<void, MemoryDeleter>;
template<typename T>
using ArrayHandle = ResourceHandle<T, ArrayDeleter<T>>;
```

### Deleters

#### `FileDeleter`
```cpp
struct FileDeleter {
    void operator()(std::FILE* file) const;
};
```

#### `MemoryDeleter`
```cpp
struct MemoryDeleter {
    void operator()(void* ptr) const;
};
```

#### `ArrayDeleter<T>`
```cpp
template<typename T>
struct ArrayDeleter {
    void operator()(T* ptr) const;
};
```

### Factory Functions

```cpp
template<typename T, typename... Args>
ResourceHandle<T> makeResource(Args&&... args);

template<typename T, typename... Args>
SharedResource<T> makeSharedResource(Args&&... args);

template<typename T>
ArrayHandle<T> makeArray(size_t size);

template<typename Func>
ScopeGuard<Func> makeScopeGuard(Func func);
```

**Example:**
```cpp
auto handle = makeResource<MyClass>(arg1, arg2);
auto shared = makeSharedResource<MyClass>(arg1, arg2);
auto array = makeArray<int>(100);
auto guard = makeScopeGuard([]() { cleanup(); });
```

### Classes

#### `FileResource`

RAII file handle wrapper.

**Constructor:**
```cpp
FileResource(const std::string& filename, const std::string& mode);
```

**Methods:**
```cpp
std::FILE* get() const;
bool isOpen() const;
void close();
const std::string& filename() const;
const std::string& mode() const;
void write(const std::string& data);
std::string readAll();
```

**Example:**
```cpp
FileResource file("data.txt", "w");
file.write("Hello, World!");
// File automatically closed when file goes out of scope
```

#### `RefCounter`

Reference counter for shared resources.

**Methods:**
```cpp
RefCounter();
RefCounter(const RefCounter& other);
RefCounter& operator=(const RefCounter& other);
int count() const;
void release();
```

---

## Common Patterns

### Error Handling Pattern

```cpp
try {
    // Operation that may fail
    auto value = parser.parse(json);
} catch (const ParseError& e) {
    // Handle parse error
    std::cerr << "Parse error: " << e.what() << std::endl;
} catch (const ResourceError& e) {
    // Handle resource error
    std::cerr << "Resource error: " << e.what() << std::endl;
} catch (const std::exception& e) {
    // Handle other errors
    std::cerr << "Error: " << e.what() << std::endl;
}
```

### RAII Pattern

```cpp
void processFile(const std::string& filename) {
    // Resource acquired
    FileResource file(filename, "r");
    
    // Use resource
    std::string content = file.readAll();
    process(content);
    
    // Resource automatically released when function exits
}
```

### Factory Pattern

```cpp
std::unique_ptr<Logger> createLogger(const std::string& type) {
    if (type == "console") {
        return std::make_unique<ConsoleLogger>("App");
    } else if (type == "file") {
        return std::make_unique<FileLogger>("App", "app.log");
    }
    return nullptr;
}
```

### Template Pattern

```cpp
template<typename T>
class Container {
    std::vector<T> items_;
public:
    void add(const T& item) {
        items_.push_back(item);
    }
    
    size_t size() const {
        return items_.size();
    }
};
```

---

**Last Updated**: 2025-12-18
**Version**: 1.0
**Status**: Complete
