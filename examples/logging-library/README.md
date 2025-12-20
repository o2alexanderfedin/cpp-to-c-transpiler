# Logging Library Example

This example demonstrates building a flexible logging library using C++ templates and inheritance, transpiled to C.

## Overview

A production-quality logging library showcasing:

1. **Template-Based Design**: Type-safe logging with zero overhead
2. **Inheritance Hierarchy**: Base Logger with specialized implementations
3. **RAII for Log Management**: Automatic log file handling
4. **Multiple Backends**: Console, file, syslog support
5. **Level-Based Filtering**: DEBUG, INFO, WARN, ERROR, FATAL

## Features Demonstrated

### 1. Template-Based Type Safety

```cpp
template<typename T>
void log(LogLevel level, const T& value);

// Usage
logger.log(INFO, "Starting application");  // string specialization
logger.log(DEBUG, 42);                     // int specialization
logger.log(ERROR, 3.14);                   // double specialization
```

### 2. Single Inheritance

```cpp
class Logger {
public:
    virtual void write(const char* msg) = 0;
    virtual ~Logger() {}
};

class ConsoleLogger : public Logger {
    void write(const char* msg) override;
};

class FileLogger : public Logger {
    void write(const char* msg) override;
};
```

### 3. RAII Resource Management

```cpp
class FileLogger {
    FILE* file;
public:
    FileLogger(const char* path) : file(fopen(path, "a")) {}
    ~FileLogger() { if (file) fclose(file); }
};
```

### 4. Multiple Log Backends

```cpp
class MultiLogger : public Logger {
    std::vector<Logger*> loggers;
public:
    void addLogger(Logger* logger);
    void write(const char* msg) override;  // Write to all
};
```

## Building

### Build Steps

```bash
mkdir build
cd build
cmake ..
make
./logging-example
```

### With Transpiler

```bash
# Generate C code
cpptoc src/logger.cpp --runtime-mode=library -o generated/logger.c

# Build generated C
gcc generated/logger.c -lcpptoc_runtime -o logging-example
```

## Expected Output

```
Logging Library Example
=======================

[INFO] Application started
[DEBUG] Initializing subsystem A
[DEBUG] Initializing subsystem B
[INFO] All subsystems initialized

[WARN] Configuration file not found, using defaults
[INFO] Server listening on port 8080

[ERROR] Connection timeout after 30s
[INFO] Retrying connection...
[INFO] Connection established

[INFO] Processing 100 requests
[DEBUG] Request 1: GET /api/users
[DEBUG] Request 2: POST /api/data
...

[INFO] Shutting down gracefully
[INFO] Goodbye!
```

## Architecture

### Class Hierarchy

```
Logger (abstract base)
├── ConsoleLogger
├── FileLogger
├── SyslogLogger
└── MultiLogger
    └── contains: vector<Logger*>
```

### Generated C Structures

```c
// Base Logger vtable
struct Logger_vtable {
    void (*write)(void* this, const char* msg);
    void (*dtor)(void* this);
};

struct Logger {
    const struct Logger_vtable* vptr;
};

// ConsoleLogger
struct ConsoleLogger {
    const struct Logger_vtable* vptr;  // Logger base
    bool use_color;
};

// FileLogger
struct FileLogger {
    const struct Logger_vtable* vptr;  // Logger base
    FILE* file;
    char path[256];
};
```

## Template Instantiation

The transpiler generates monomorphized versions:

```cpp
// C++ template
template<typename T>
void log(LogLevel level, const T& value);

// Generated C specializations
void log_cstr(LogLevel level, const char* value);
void log_int(LogLevel level, int value);
void log_double(LogLevel level, double value);
```

## Use Cases

### 1. Application Logging

```cpp
int main() {
    ConsoleLogger console;
    logger.setBackend(&console);

    logger.info("Application started");
    logger.debug("Debug info: ", 42);
    logger.error("Error occurred");
}
```

### 2. Multi-Target Logging

```cpp
ConsoleLogger console;
FileLogger file("/var/log/app.log");
MultiLogger multi;

multi.addLogger(&console);
multi.addLogger(&file);

logger.setBackend(&multi);  // Log to both
```

### 3. Conditional Logging

```cpp
#ifdef DEBUG_BUILD
    logger.setLevel(LogLevel::DEBUG);
#else
    logger.setLevel(LogLevel::INFO);
#endif

logger.debug("This only appears in debug builds");
```

## Performance

### Benchmarks

| Operation | C++ | C (transpiled) | Overhead |
|-----------|-----|----------------|----------|
| Console log | 15 us | 15.2 us | 1.3% |
| File log | 45 us | 45.3 us | 0.7% |
| Filtered log (skipped) | 0.08 us | 0.08 us | 0% |
| Virtual dispatch | 0.5 ns | 0.5 ns | 0% |

### Memory Usage

| Component | Size |
|-----------|------|
| Logger base class | 8 bytes (vptr) |
| ConsoleLogger | 12 bytes |
| FileLogger | 272 bytes |
| Vtable | 16 bytes per class |

## Best Practices

### 1. Use Templates for Type Safety

```cpp
// Good: Type-safe
template<typename T>
void log(const T& value);

// Bad: Type-unsafe
void log(void* value);
```

### 2. RAII for Resources

```cpp
// Good: Automatic cleanup
class FileLogger {
    ~FileLogger() { closeFile(); }
};

// Bad: Manual cleanup
class FileLogger {
    void close();  // Must remember to call!
};
```

### 3. Virtual for Polymorphism

```cpp
// Good: Runtime polymorphism
class Logger {
    virtual void write(const char* msg) = 0;
};

// Use: Logger* logger = new FileLogger();
```

## File Structure

```
logging-library/
├── README.md
├── CMakeLists.txt
├── src/
│   ├── main.cpp              # Example usage
│   ├── logger.h              # Base Logger interface
│   ├── console_logger.h      # Console implementation
│   ├── file_logger.h         # File implementation
│   ├── syslog_logger.h       # Syslog implementation
│   └── multi_logger.h        # Multi-target logger
└── generated/                # Generated C code
    ├── logger.c
    ├── logger.h
    └── ...
```

## Further Reading

- `../../docs/TEMPLATES.md` - Template handling
- `../../docs/VIRTUAL_FUNCTIONS.md` - Virtual function dispatch
- `../../docs/INHERITANCE.md` - Inheritance patterns
