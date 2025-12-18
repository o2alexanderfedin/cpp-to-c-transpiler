# Real-World Testing Scenarios

Comprehensive testing scenarios for validating C++ to C transpilation.

## Overview

This document describes detailed testing scenarios that validate the transpiler handles real-world use cases correctly.

## JSON Parser Scenarios

### Scenario 1: Configuration File Parsing

**Description**: Parse application configuration from JSON file

**Input JSON**:
```json
{
  "server": {
    "host": "0.0.0.0",
    "port": 8080,
    "workers": 4
  },
  "database": {
    "host": "localhost",
    "port": 5432,
    "name": "mydb",
    "pool_size": 10
  },
  "features": {
    "caching": true,
    "compression": false,
    "logging": "verbose"
  }
}
```

**Test Code**:
```cpp
JsonParser parser;
auto config = parser.parse(jsonString);

const auto& server = config->asObject()["server"].asObject();
assert(server["host"].asString() == "0.0.0.0");
assert(server["port"].asNumber() == 8080);
assert(server["workers"].asNumber() == 4);

const auto& db = config->asObject()["database"].asObject();
assert(db["name"].asString() == "mydb");
assert(db["pool_size"].asNumber() == 10);

const auto& features = config->asObject()["features"].asObject();
assert(features["caching"].asBool() == true);
assert(features["compression"].asBool() == false);
```

**Expected Result**: All assertions pass

**Transpilation Validation**:
- Virtual method calls translated correctly
- Map operations work in C
- String comparisons work
- Type conversions accurate

### Scenario 2: API Response Parsing

**Description**: Parse paginated API response with nested user data

**Input JSON**:
```json
{
  "status": "success",
  "page": 1,
  "per_page": 10,
  "total": 42,
  "data": [
    {
      "id": 1,
      "username": "alice",
      "email": "alice@example.com",
      "roles": ["admin", "user"],
      "active": true
    },
    {
      "id": 2,
      "username": "bob",
      "email": "bob@example.com",
      "roles": ["user"],
      "active": false
    }
  ]
}
```

**Test Code**:
```cpp
JsonParser parser;
auto response = parser.parse(jsonString);

const auto& obj = response->asObject();
assert(obj["status"].asString() == "success");
assert(obj["total"].asNumber() == 42);

const auto& users = obj["data"].asArray();
assert(users.size() == 2);

const auto& user1 = users[0].asObject();
assert(user1["username"].asString() == "alice");
assert(user1["active"].asBool() == true);

const auto& roles1 = user1["roles"].asArray();
assert(roles1.size() == 2);
assert(roles1[0].asString() == "admin");
```

**Expected Result**: All assertions pass

### Scenario 3: Error Handling

**Description**: Gracefully handle malformed JSON

**Test Cases**:
1. Missing closing brace: `{"key": "value"`
2. Trailing comma: `{"key": "value",}`
3. Unquoted key: `{key: "value"}`
4. Invalid escape: `{"key": "\x"}`
5. Unterminated string: `{"key": "value`

**Test Code**:
```cpp
std::vector<std::string> invalidCases = {
    "{\"key\": \"value\"",
    "{\"key\": \"value\",}",
    "{key: \"value\"}",
    "{\"key\": \"\\x\"}",
    "{\"key\": \"value"
};

for (const auto& invalidJson : invalidCases) {
    bool caught = false;
    try {
        parser.parse(invalidJson);
    } catch (const ParseError&) {
        caught = true;
    }
    assert(caught == true);
}
```

**Expected Result**: All invalid JSON throws ParseError

## Logger Scenarios

### Scenario 4: Application Lifecycle Logging

**Description**: Log complete application startup/shutdown sequence

**Test Code**:
```cpp
FileLogger logger("App", "lifecycle.log", LogLevel::INFO, false);

logger.info("========== Application Starting ==========");
logger.info("Version: 1.0.0");
logger.info("PID: 12345");

logger.info("Initializing subsystems...");
logger.info("  - Database: OK");
logger.info("  - Cache: OK");
logger.info("  - Network: OK");

logger.info("Ready to accept connections");
logger.info("Listening on 0.0.0.0:8080");

// Simulate runtime
logger.info("Processing request #1");
logger.warn("Connection pool 80% full");
logger.error("Request #2 failed: timeout");

logger.info("Shutting down...");
logger.info("  - Closing connections");
logger.info("  - Flushing cache");
logger.info("  - Closing database");
logger.info("========== Application Stopped ==========");
```

**Validation**:
1. File created and written
2. All messages present
3. Timestamps increasing
4. Correct log levels
5. File properly closed

### Scenario 5: Multi-Destination Error Tracking

**Description**: Log errors to multiple destinations for redundancy

**Test Code**:
```cpp
MultiLogger errorLogger("ErrorTracker", LogLevel::ERROR);

errorLogger.addLogger(std::make_unique<ConsoleLogger>("Console", LogLevel::ERROR));
errorLogger.addLogger(std::make_unique<FileLogger>("Primary", "errors.log", LogLevel::ERROR));
errorLogger.addLogger(std::make_unique<FileLogger>("Backup", "errors_backup.log", LogLevel::ERROR));

try {
    throw std::runtime_error("Database connection lost");
} catch (const std::exception& e) {
    errorLogger.error("Exception caught: " + std::string(e.what()));
    errorLogger.error("Stack trace: ...");
    errorLogger.error("Request ID: 12345");
    errorLogger.error("User: alice@example.com");
}
```

**Validation**:
1. Error appears in all 3 destinations
2. Console output visible
3. Both files contain same content
4. All messages have timestamps

### Scenario 6: Performance Logging

**Description**: Log timing information for performance analysis

**Test Code**:
```cpp
FileLogger perfLogger("Performance", "perf.log", LogLevel::INFO);

auto start = std::chrono::steady_clock::now();

perfLogger.info("Starting batch processing");

for (int batch = 0; batch < 10; ++batch) {
    auto batchStart = std::chrono::steady_clock::now();
    
    // Simulate work
    std::this_thread::sleep_for(std::chrono::milliseconds(100));
    
    auto batchEnd = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(batchEnd - batchStart);
    
    perfLogger.info("Batch " + std::to_string(batch) + " completed in " + 
                   std::to_string(duration.count()) + "ms");
}

auto end = std::chrono::steady_clock::now();
auto total = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);

perfLogger.info("Total processing time: " + std::to_string(total.count()) + "ms");
```

**Validation**:
1. Individual batch times logged
2. Total time approximately correct
3. Timing data parseable

## Test Framework Scenarios

### Scenario 7: Database Integration Testing

**Description**: Test database operations with fixtures

**Test Code**:
```cpp
class DatabaseTest : public TestCase {
protected:
    MockDatabase* db;
    
    void setUp() override {
        db = new MockDatabase();
        db->connect("test.db");
        db->execute("CREATE TABLE users (id INT, name TEXT)");
    }
    
    void tearDown() override {
        db->execute("DROP TABLE users");
        db->disconnect();
        delete db;
    }
    
public:
    DatabaseTest(const std::string& name) : TestCase(name) {}
};

class InsertTest : public DatabaseTest {
public:
    InsertTest() : DatabaseTest("Insert") {}
    
    void run() override {
        db->execute("INSERT INTO users VALUES (1, 'Alice')");
        auto result = db->query("SELECT COUNT(*) FROM users");
        ASSERT_EQ(result.getInt(0), 1);
    }
};

class UpdateTest : public DatabaseTest {
public:
    UpdateTest() : DatabaseTest("Update") {}
    
    void run() override {
        db->execute("INSERT INTO users VALUES (1, 'Alice')");
        db->execute("UPDATE users SET name = 'Bob' WHERE id = 1");
        auto result = db->query("SELECT name FROM users WHERE id = 1");
        ASSERT_EQ(result.getString(0), "Bob");
    }
};
```

**Validation**:
1. setUp called before each test
2. tearDown called after each test
3. Tests independent (order doesn't matter)
4. Database cleaned up after failures

### Scenario 8: Exception Testing

**Description**: Verify exception handling in tests

**Test Code**:
```cpp
class ExceptionTest : public TestCase {
public:
    ExceptionTest() : TestCase("ExceptionTest") {}
    
    void run() override {
        // Should throw
        ASSERT_THROW(divide(1, 0));
        
        // Should throw specific type
        ASSERT_THROW_TYPE(
            parser.parse("invalid"),
            ParseError
        );
        
        // Should not throw
        bool thrown = false;
        try {
            ASSERT_THROW(safeOperation());
        } catch (...) {
            thrown = true;
        }
        ASSERT_TRUE(thrown); // Because safeOperation doesn't throw
    }
};
```

**Validation**:
1. ASSERT_THROW detects exceptions
2. ASSERT_THROW_TYPE validates exception type
3. Missing exceptions caught as test failures

## String Formatter Scenarios

### Scenario 9: Report Generation

**Description**: Generate formatted business report

**Test Code**:
```cpp
StringBuilder report;

report << "=== Sales Report ===" << "\n\n";

report << formatters::pad("Product", 20, Align::Left);
report << formatters::pad("Sales", 10, Align::Right);
report << formatters::pad("Revenue", 12, Align::Right) << "\n";

report << std::string(42, '-') << "\n";

struct Product {
    std::string name;
    int sales;
    double revenue;
};

std::vector<Product> products = {
    {"Widget A", 150, 15000.50},
    {"Widget B", 200, 25000.75},
    {"Widget C", 100, 10000.25}
};

double totalRevenue = 0;

for (const auto& p : products) {
    report << formatters::pad(p.name, 20, Align::Left);
    report << formatters::pad(std::to_string(p.sales), 10, Align::Right);
    report << formatters::pad(formatters::fixed(p.revenue, 2), 12, Align::Right);
    report << "\n";
    totalRevenue += p.revenue;
}

report << std::string(42, '-') << "\n";
report << formatters::pad("TOTAL", 30, Align::Right);
report << formatters::pad(formatters::fixed(totalRevenue, 2), 12, Align::Right);

std::cout << report.str();
```

**Expected Output**:
```
=== Sales Report ===

Product             Sales       Revenue
------------------------------------------
Widget A              150     15000.50
Widget B              200     25000.75
Widget C              100     10000.25
------------------------------------------
                        TOTAL  50001.50
```

**Validation**:
1. Columns aligned correctly
2. Numbers formatted with 2 decimals
3. Totals calculated correctly
4. Report readable

### Scenario 10: Log Message Formatting

**Description**: Format structured log messages

**Test Code**:
```cpp
std::string requestId = "REQ-12345";
std::string userId = "USER-789";
std::string operation = "UPDATE";
std::string resource = "/api/users/42";
int statusCode = 200;
double responseTime = 0.125;

std::string logMessage = formatString(
    "[{0}] [{1}] {2} {3} - {4} ({5}ms)",
    requestId,
    userId,
    operation,
    resource,
    statusCode,
    formatters::fixed(responseTime * 1000, 2)
);

std::cout << logMessage << std::endl;
```

**Expected Output**:
```
[REQ-12345] [USER-789] UPDATE /api/users/42 - 200 (125.00ms)
```

**Validation**:
1. Placeholders replaced correctly
2. Response time formatted correctly
3. Order preserved

## Resource Manager Scenarios

### Scenario 11: Connection Pool Management

**Description**: Manage database connections with pooling

**Test Code**:
```cpp
ResourcePool<DatabaseConnection> pool(5);

// Initialize pool
for (int i = 0; i < 5; ++i) {
    auto conn = std::make_unique<DatabaseConnection>();
    conn->connect("database.db");
    pool.add(std::move(conn));
}

// Use connections
{
    PooledResource<DatabaseConnection> conn1(pool);
    conn1->execute("SELECT * FROM users");
    
    {
        PooledResource<DatabaseConnection> conn2(pool);
        conn2->execute("UPDATE users SET active = 1");
    } // conn2 released
    
    PooledResource<DatabaseConnection> conn3(pool);
    conn3->execute("DELETE FROM sessions WHERE expired = 1");
    
} // conn1, conn3 released

assert(pool.available() == 5);
assert(pool.inUse() == 0);
```

**Validation**:
1. Pool initialized correctly
2. Connections acquired successfully
3. Connections automatically released
4. Pool state correct after use

### Scenario 12: File Resource Management

**Description**: Handle multiple files with RAII

**Test Code**:
```cpp
void processFiles(const std::vector<std::string>& filenames) {
    std::vector<FileResource> files;
    
    // Open all files
    for (const auto& filename : filenames) {
        files.emplace_back(filename, "r");
    }
    
    // Process files
    for (auto& file : files) {
        std::string content = file.readAll();
        process(content);
    }
    
    // All files automatically closed when function returns
}
```

**Validation**:
1. All files opened successfully
2. Content read correctly
3. All files closed automatically
4. No resource leaks

### Scenario 13: Memory Pool Performance

**Description**: Benchmark memory pool vs direct allocation

**Test Code**:
```cpp
const int ITERATIONS = 10000;

// Direct allocation
auto start1 = std::chrono::high_resolution_clock::now();
for (int i = 0; i < ITERATIONS; ++i) {
    int* ptr = new int(i);
    delete ptr;
}
auto end1 = std::chrono::high_resolution_clock::now();
auto direct_time = std::chrono::duration_cast<std::chrono::microseconds>(end1 - start1);

// Pool allocation
MemoryPool<int> pool(1000);
auto start2 = std::chrono::high_resolution_clock::now();
for (int i = 0; i < ITERATIONS; ++i) {
    int* ptr = pool.allocate();
    *ptr = i;
    pool.deallocate(ptr);
}
auto end2 = std::chrono::high_resolution_clock::now();
auto pool_time = std::chrono::duration_cast<std::chrono::microseconds>(end2 - start2);

double speedup = static_cast<double>(direct_time.count()) / pool_time.count();
assert(speedup > 1.0); // Pool should be faster
```

**Validation**:
1. Both methods produce same results
2. Pool allocation faster than direct
3. No memory leaks in either case

## Integration Scenarios

### Scenario 14: Complete Web Server Simulation

**Description**: Simulate web server handling requests

**Test Code**:
```cpp
class WebServer {
    MultiLogger logger_;
    ResourcePool<Connection> connPool_;
    
public:
    WebServer() : logger_("Server", LogLevel::INFO), connPool_(10) {
        logger_.addLogger(std::make_unique<ConsoleLogger>("Console", LogLevel::WARN));
        logger_.addLogger(std::make_unique<FileLogger>("Access", "access.log", LogLevel::INFO));
        logger_.addLogger(std::make_unique<FileLogger>("Error", "error.log", LogLevel::ERROR));
        
        for (int i = 0; i < 10; ++i) {
            connPool_.add(std::make_unique<Connection>());
        }
    }
    
    void handleRequest(const std::string& jsonRequest) {
        logger_.info("Request received");
        
        try {
            JsonParser parser;
            auto request = parser.parse(jsonRequest);
            
            PooledResource<Connection> conn(connPool_);
            
            const auto& obj = request->asObject();
            std::string method = obj["method"].asString();
            std::string path = obj["path"].asString();
            
            logger_.info(formatString("{} {}", method, path));
            
            std::string response = conn->process(request);
            
            logger_.info("Request completed successfully");
            
        } catch (const ParseError& e) {
            logger_.error("Invalid request: " + std::string(e.what()));
        } catch (const ResourceError& e) {
            logger_.error("Resource error: " + std::string(e.what()));
        }
    }
};
```

**Validation**:
1. Logger setup correctly
2. Connection pool initialized
3. Requests parsed and processed
4. Errors logged appropriately
5. Resources cleaned up

### Scenario 15: Data Pipeline

**Description**: Process data through multiple stages

**Test Code**:
```cpp
class DataPipeline {
    FileLogger logger_;
    
public:
    DataPipeline() : logger_("Pipeline", "pipeline.log", LogLevel::DEBUG) {}
    
    void process(const std::string& inputFile, const std::string& outputFile) {
        logger_.info("Starting pipeline");
        
        // Stage 1: Load data
        FileResource input(inputFile, "r");
        std::string rawData = input.readAll();
        logger_.debug("Loaded " + std::to_string(rawData.size()) + " bytes");
        
        // Stage 2: Parse JSON
        JsonParser parser;
        auto data = parser.parse(rawData);
        logger_.debug("Parsed JSON successfully");
        
        // Stage 3: Transform data
        auto transformed = transform(data);
        logger_.debug("Transformed data");
        
        // Stage 4: Format output
        StringBuilder output;
        output << "Results:\n";
        output << transformed->toString();
        logger_.debug("Formatted output");
        
        // Stage 5: Write results
        FileResource outputFile(outputFile, "w");
        outputFile.write(output.str());
        logger_.info("Pipeline completed");
    }
};
```

**Validation**:
1. All stages execute in order
2. Data transformed correctly
3. Output file written
4. Logging captures progress
5. Resources cleaned up

## Performance Benchmarks

### Scenario 16: JSON Parser Benchmark

**Test Code**:
```cpp
const int ITERATIONS = 1000;
std::string largeJson = generateLargeJSON(10000); // 10K elements

auto start = std::chrono::high_resolution_clock::now();

for (int i = 0; i < ITERATIONS; ++i) {
    JsonParser parser;
    auto value = parser.parse(largeJson);
}

auto end = std::chrono::high_resolution_clock::now();
auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);

double avg_time = static_cast<double>(duration.count()) / ITERATIONS;
std::cout << "Average parse time: " << avg_time << "ms" << std::endl;

assert(avg_time < 10.0); // Should parse in < 10ms
```

### Scenario 17: Logger Throughput

**Test Code**:
```cpp
const int MESSAGES = 100000;

FileLogger logger("Bench", "bench.log", LogLevel::INFO, false);

auto start = std::chrono::high_resolution_clock::now();

for (int i = 0; i < MESSAGES; ++i) {
    logger.info("Log message " + std::to_string(i));
}

auto end = std::chrono::high_resolution_clock::now();
auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);

double throughput = static_cast<double>(MESSAGES) / duration.count() * 1000;
std::cout << "Throughput: " << throughput << " messages/second" << std::endl;

assert(throughput > 10000); // Should handle > 10K msg/sec
```

## Summary

These scenarios cover:
- ✓ Real-world use cases
- ✓ Integration testing
- ✓ Error handling
- ✓ Performance benchmarks
- ✓ Resource management
- ✓ Complex workflows

Each scenario validates:
1. Functional correctness
2. Error handling
3. Resource cleanup
4. Performance characteristics
5. Transpilation compatibility

---

**Version**: 1.0
**Last Updated**: 2025-12-18
**Status**: Complete
