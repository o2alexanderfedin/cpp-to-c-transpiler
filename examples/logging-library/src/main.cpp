// Logging Library Example
// Demonstrates templates, inheritance, and virtual functions

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>

// ============================================================================
// Log Levels
// ============================================================================

enum class LogLevel {
    DEBUG = 0,
    INFO = 1,
    WARN = 2,
    ERROR = 3,
    FATAL = 4
};

const char* logLevelToString(LogLevel level) {
    switch (level) {
        case LogLevel::DEBUG: return "DEBUG";
        case LogLevel::INFO:  return "INFO";
        case LogLevel::WARN:  return "WARN";
        case LogLevel::ERROR: return "ERROR";
        case LogLevel::FATAL: return "FATAL";
        default: return "UNKNOWN";
    }
}

// ============================================================================
// Base Logger Interface
// ============================================================================

class Logger {
protected:
    LogLevel min_level;

public:
    Logger() : min_level(LogLevel::INFO) {}
    virtual ~Logger() {}

    virtual void write(LogLevel level, const char* msg) = 0;

    void setLevel(LogLevel level) {
        min_level = level;
    }

    bool shouldLog(LogLevel level) const {
        return level >= min_level;
    }
};

// ============================================================================
// Console Logger
// ============================================================================

class ConsoleLogger : public Logger {
    bool use_color;

public:
    ConsoleLogger(bool color = true) : use_color(color) {}

    void write(LogLevel level, const char* msg) override {
        if (!shouldLog(level)) return;

        // Get timestamp
        time_t now = time(nullptr);
        char timestamp[32];
        strftime(timestamp, sizeof(timestamp), "%H:%M:%S", localtime(&now));

        // Color codes (ANSI)
        const char* color = "";
        const char* reset = "";
        if (use_color) {
            reset = "\033[0m";
            switch (level) {
                case LogLevel::DEBUG: color = "\033[36m"; break;  // Cyan
                case LogLevel::INFO:  color = "\033[32m"; break;  // Green
                case LogLevel::WARN:  color = "\033[33m"; break;  // Yellow
                case LogLevel::ERROR: color = "\033[31m"; break;  // Red
                case LogLevel::FATAL: color = "\033[35m"; break;  // Magenta
            }
        }

        printf("%s[%s] [%s]%s %s\n",
               color,
               timestamp,
               logLevelToString(level),
               reset,
               msg);
    }
};

// ============================================================================
// File Logger
// ============================================================================

class FileLogger : public Logger {
    FILE* file;
    char path[256];
    size_t bytes_written;

public:
    FileLogger(const char* filepath) : file(nullptr), bytes_written(0) {
        strncpy(path, filepath, sizeof(path) - 1);
        path[sizeof(path) - 1] = '\0';

        file = fopen(path, "a");
        if (!file) {
            fprintf(stderr, "Failed to open log file: %s\n", path);
        }
    }

    ~FileLogger() {
        if (file) {
            fclose(file);
        }
    }

    void write(LogLevel level, const char* msg) override {
        if (!shouldLog(level) || !file) return;

        // Get timestamp
        time_t now = time(nullptr);
        char timestamp[32];
        strftime(timestamp, sizeof(timestamp), "%Y-%m-%d %H:%M:%S", localtime(&now));

        // Write to file
        int written = fprintf(file, "[%s] [%s] %s\n",
                             timestamp,
                             logLevelToString(level),
                             msg);

        if (written > 0) {
            bytes_written += written;
            fflush(file);  // Ensure it's written immediately
        }
    }

    size_t getBytesWritten() const { return bytes_written; }
};

// ============================================================================
// Multi-Logger (writes to multiple backends)
// ============================================================================

class MultiLogger : public Logger {
    Logger* loggers[8];
    size_t count;

public:
    MultiLogger() : count(0) {}

    void addLogger(Logger* logger) {
        if (count < 8) {
            loggers[count++] = logger;
        }
    }

    void write(LogLevel level, const char* msg) override {
        for (size_t i = 0; i < count; i++) {
            loggers[i]->write(level, msg);
        }
    }
};

// ============================================================================
// Template-Based Logging Functions
// ============================================================================

// Template-based logging (inline for header-only pattern)
template<typename T>
inline void logValue(Logger& logger, LogLevel level, const T& value) {
    // Default: convert to string (would need specialization)
}

// Specialization for C strings
template<>
inline void logValue<const char*>(Logger& logger, LogLevel level, const char* const& value) {
    logger.write(level, value);
}

// Specialization for integers
template<>
inline void logValue<int>(Logger& logger, LogLevel level, const int& value) {
    char buffer[32];
    snprintf(buffer, sizeof(buffer), "%d", value);
    logger.write(level, buffer);
}

// Specialization for doubles
template<>
inline void logValue<double>(Logger& logger, LogLevel level, const double& value) {
    char buffer[32];
    snprintf(buffer, sizeof(buffer), "%.2f", value);
    logger.write(level, buffer);
}

// ============================================================================
// Convenience Functions
// ============================================================================

class LoggerWrapper {
    Logger* backend;

public:
    LoggerWrapper(Logger* logger = nullptr) : backend(logger) {}

    void setBackend(Logger* logger) {
        backend = logger;
    }

    void debug(const char* msg) {
        if (backend) backend->write(LogLevel::DEBUG, msg);
    }

    void info(const char* msg) {
        if (backend) backend->write(LogLevel::INFO, msg);
    }

    void warn(const char* msg) {
        if (backend) backend->write(LogLevel::WARN, msg);
    }

    void error(const char* msg) {
        if (backend) backend->write(LogLevel::ERROR, msg);
    }

    void fatal(const char* msg) {
        if (backend) backend->write(LogLevel::FATAL, msg);
    }

    template<typename T>
    void log(LogLevel level, const T& value) {
        if (backend) logValue(*backend, level, value);
    }
};

// ============================================================================
// Example Application
// ============================================================================

void simulateApplicationStartup(LoggerWrapper& logger) {
    logger.info("Application started");
    logger.debug("Initializing subsystem A");
    logger.debug("Initializing subsystem B");
    logger.info("All subsystems initialized");
}

void simulateConfiguration(LoggerWrapper& logger) {
    logger.warn("Configuration file not found, using defaults");
    logger.info("Server listening on port 8080");
}

void simulateNetworkError(LoggerWrapper& logger) {
    logger.error("Connection timeout after 30s");
    logger.info("Retrying connection...");
    logger.info("Connection established");
}

void simulateProcessing(LoggerWrapper& logger) {
    logger.info("Processing 100 requests");

    // Simulate some requests
    for (int i = 1; i <= 5; i++) {
        char buffer[128];
        snprintf(buffer, sizeof(buffer), "Request %d: GET /api/data", i);
        logger.debug(buffer);
    }

    logger.info("All requests processed successfully");
}

void simulateShutdown(LoggerWrapper& logger) {
    logger.info("Shutting down gracefully");
    logger.info("Goodbye!");
}

// ============================================================================
// Main
// ============================================================================

int main() {
    printf("Logging Library Example\n");
    printf("=======================\n\n");

    // Example 1: Console Logger
    printf("=== Example 1: Console Logger ===\n");
    {
        ConsoleLogger console(true);  // With color
        console.setLevel(LogLevel::DEBUG);
        LoggerWrapper logger(&console);

        simulateApplicationStartup(logger);
        simulateConfiguration(logger);
    }

    printf("\n=== Example 2: File Logger ===\n");
    {
        FileLogger file("/tmp/app.log");
        file.setLevel(LogLevel::INFO);
        LoggerWrapper logger(&file);

        logger.info("This goes to file");
        logger.debug("This is filtered out (level too low)");
        logger.error("Error logged to file");

        printf("Logged %zu bytes to /tmp/app.log\n", file.getBytesWritten());
    }

    printf("\n=== Example 3: Multi-Logger (Console + File) ===\n");
    {
        ConsoleLogger console(false);  // No color for clarity
        FileLogger file("/tmp/multi.log");

        MultiLogger multi;
        multi.addLogger(&console);
        multi.addLogger(&file);
        multi.setLevel(LogLevel::INFO);

        LoggerWrapper logger(&multi);

        simulateNetworkError(logger);
        simulateProcessing(logger);
        simulateShutdown(logger);
    }

    printf("\n=== Example 4: Template Logging ===\n");
    {
        ConsoleLogger console(false);
        LoggerWrapper logger(&console);

        logger.log(LogLevel::INFO, "String message");
        logger.log(LogLevel::DEBUG, 42);
        logger.log(LogLevel::WARN, 3.14159);
    }

    printf("\n=== All examples completed successfully ===\n");

    return 0;
}
