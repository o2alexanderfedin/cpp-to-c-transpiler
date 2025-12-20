#include "Logger.h"
#include <iostream>
#include <thread>
#include <chrono>
#include <vector>

using namespace logging;

// Example 1: Basic console logging
void exampleBasicConsoleLogging() {
    ConsoleLogger logger("App", LogLevel::DEBUG);

    logger.debug("This is a debug message");
    logger.info("Application started");
    logger.warn("Low memory warning");
    logger.error("Failed to connect to database");
    logger.fatal("Critical system error");
}

// Example 2: File logging with different levels
void exampleFileLogging() {
    FileLogger logger("FileExample", "app.log", LogLevel::INFO, false);

    logger.info("Application initialized");
    logger.info("Loading configuration from config.json");
    logger.warn("Configuration file missing optional field 'timeout'");
    logger.info("Server starting on port 8080");
    logger.error("Failed to bind to port 8080");
    logger.info("Retrying on port 8081");
    logger.info("Server successfully started on port 8081");
}

// Example 3: Multiple loggers
void exampleMultipleLoggers() {
    ConsoleLogger consoleLogger("Console", LogLevel::INFO);
    FileLogger fileLogger("File", "debug.log", LogLevel::DEBUG, false);
    FileLogger errorLogger("Errors", "errors.log", LogLevel::ERROR, false);

    std::vector<std::string> operations = {
        "Connecting to database",
        "Querying user table",
        "Processing results",
        "Updating cache",
        "Responding to client"
    };

    for (const auto& op : operations) {
        fileLogger.debug("Starting: " + op);
        consoleLogger.info(op);

        if (op.find("Querying") != std::string::npos) {
            errorLogger.error("Database query failed: timeout");
        }

        fileLogger.debug("Completed: " + op);
    }
}

// Example 4: Stream-style logging
void exampleStreamStyleLogging() {
    ConsoleLogger logger("Stream", LogLevel::DEBUG);

    debug(logger) << "Debug message with value: " << 42;
    info(logger) << "Processing " << 100 << " items";
    warn(logger) << "Cache size: " << 95 << "% full";
    error(logger) << "Connection failed after " << 3 << " retries";
}

// Example 5: Multi-target logging
void exampleMultiTargetLogging() {
    MultiLogger multi("MultiTarget", LogLevel::DEBUG);

    multi.addLogger(std::make_unique<ConsoleLogger>("Console", LogLevel::INFO));
    multi.addLogger(std::make_unique<FileLogger>("File1", "app.log", LogLevel::DEBUG, false));
    multi.addLogger(std::make_unique<FileLogger>("File2", "backup.log", LogLevel::INFO, false));

    multi.debug("Debug message (only to file1)");
    multi.info("Info message (to all loggers)");
    multi.warn("Warning message (to all loggers)");
    multi.error("Error message (to all loggers)");
}

// Example 6: Log level filtering
void exampleLogLevelFiltering() {
    ConsoleLogger logger("Filtering", LogLevel::WARN);

    logger.debug("This won't be logged");
    logger.info("This won't be logged");
    logger.warn("This will be logged");
    logger.error("This will be logged");
    logger.fatal("This will be logged");

    logger.setLevel(LogLevel::DEBUG);
    logger.debug("Now debug messages are logged");
}

// Example 7: Application lifecycle logging
void exampleApplicationLifecycle() {
    FileLogger logger("Lifecycle", "lifecycle.log", LogLevel::INFO, false);

    logger.info("========== Application Starting ==========");
    logger.info("Version: 1.0.0");
    logger.info("Build: 2025-01-15");

    logger.info("Initializing subsystems...");
    std::this_thread::sleep_for(std::chrono::milliseconds(100));
    logger.info("  - Database connection: OK");

    std::this_thread::sleep_for(std::chrono::milliseconds(100));
    logger.info("  - Cache system: OK");

    std::this_thread::sleep_for(std::chrono::milliseconds(100));
    logger.info("  - Network services: OK");

    logger.info("Application ready");

    std::this_thread::sleep_for(std::chrono::milliseconds(500));

    logger.info("Shutting down...");
    logger.info("  - Closing database connections");
    logger.info("  - Flushing caches");
    logger.info("  - Stopping network services");
    logger.info("========== Application Stopped ==========");
}

// Example 8: Error tracking
void exampleErrorTracking() {
    FileLogger errorLog("ErrorTracker", "errors.log", LogLevel::ERROR, false);
    ConsoleLogger console("App", LogLevel::INFO);

    try {
        console.info("Processing request #1234");
        throw std::runtime_error("Database connection lost");
    } catch (const std::exception& e) {
        errorLog.error(std::string("Exception caught: ") + e.what());
        errorLog.error("Request ID: 1234");
        errorLog.error("User: john.doe@example.com");
        errorLog.error("Timestamp: 2025-01-15 14:30:00");
        console.error("Request failed - see error log for details");
    }
}

// Example 9: Performance logging
void examplePerformanceLogging() {
    FileLogger perfLog("Performance", "perf.log", LogLevel::INFO, false);

    auto start = std::chrono::steady_clock::now();

    perfLog.info("Starting data processing");

    // Simulate work
    for (int i = 0; i < 5; ++i) {
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        perfLog.info("Processed batch " + std::to_string(i + 1) + "/5");
    }

    auto end = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);

    perfLog.info("Processing completed in " + std::to_string(duration.count()) + "ms");
}

// Example 10: Configuration logging
void exampleConfigurationLogging() {
    ConsoleLogger logger("Config", LogLevel::INFO);

    logger.info("Loading configuration...");
    logger.info("  Server:");
    logger.info("    - Host: 0.0.0.0");
    logger.info("    - Port: 8080");
    logger.info("    - Workers: 4");
    logger.info("  Database:");
    logger.info("    - Type: PostgreSQL");
    logger.info("    - Host: localhost");
    logger.info("    - Port: 5432");
    logger.info("  Cache:");
    logger.info("    - Type: Redis");
    logger.info("    - TTL: 3600s");
    logger.info("Configuration loaded successfully");
}

// Example 11: Request/Response logging
void exampleRequestResponseLogging() {
    FileLogger logger("HTTP", "http.log", LogLevel::INFO, false);

    struct Request {
        std::string method;
        std::string path;
        std::string client;
    };

    std::vector<Request> requests = {
        {"GET", "/api/users", "192.168.1.100"},
        {"POST", "/api/users", "192.168.1.101"},
        {"GET", "/api/users/42", "192.168.1.100"},
        {"DELETE", "/api/users/42", "192.168.1.102"},
        {"GET", "/health", "192.168.1.103"}
    };

    for (const auto& req : requests) {
        logger.info(req.method + " " + req.path + " from " + req.client);
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
        logger.info("Response: 200 OK");
    }
}

// Example 12: Security logging
void exampleSecurityLogging() {
    FileLogger secLog("Security", "security.log", LogLevel::WARN, false);

    secLog.warn("Failed login attempt for user: admin");
    secLog.warn("Source IP: 10.0.0.50");

    secLog.warn("Multiple failed login attempts detected");
    secLog.error("Potential brute force attack from IP: 10.0.0.50");
    secLog.error("Blocking IP: 10.0.0.50");

    secLog.info("Security scan completed");
    secLog.info("  - 0 critical issues");
    secLog.warn("  - 2 warnings");
    secLog.info("  - 0 informational");
}

// Example 13: Transaction logging
void exampleTransactionLogging() {
    FileLogger txLog("Transactions", "transactions.log", LogLevel::INFO, false);

    struct Transaction {
        std::string id;
        std::string user;
        double amount;
        std::string status;
    };

    std::vector<Transaction> transactions = {
        {"TX-001", "alice@example.com", 50.00, "completed"},
        {"TX-002", "bob@example.com", 100.00, "pending"},
        {"TX-003", "charlie@example.com", 75.50, "completed"},
        {"TX-004", "dave@example.com", 200.00, "failed"}
    };

    for (const auto& tx : transactions) {
        txLog.info("Transaction " + tx.id + ":");
        txLog.info("  User: " + tx.user);
        txLog.info("  Amount: $" + std::to_string(tx.amount));
        txLog.info("  Status: " + tx.status);

        if (tx.status == "failed") {
            txLog.error("Transaction failed - insufficient funds");
        }
    }
}

// Example 14: Audit logging
void exampleAuditLogging() {
    FileLogger audit("Audit", "audit.log", LogLevel::INFO, false);

    audit.info("User login: john.doe");
    audit.info("User accessed resource: /api/sensitive/data");
    audit.warn("User attempted to access restricted resource: /admin");
    audit.error("Access denied: insufficient permissions");
    audit.info("User modified record: USER-123");
    audit.info("  Field: email");
    audit.info("  Old value: old@example.com");
    audit.info("  New value: new@example.com");
    audit.info("User logout: john.doe");
}

// Example 15: Structured logging with context
void exampleStructuredLogging() {
    ConsoleLogger logger("Structured", LogLevel::INFO);

    std::string requestId = "REQ-12345";
    std::string userId = "USER-789";

    logger.info("[" + requestId + "] [" + userId + "] Request received");
    logger.info("[" + requestId + "] [" + userId + "] Validating input");
    logger.info("[" + requestId + "] [" + userId + "] Processing data");
    logger.warn("[" + requestId + "] [" + userId + "] Slow query detected (250ms)");
    logger.info("[" + requestId + "] [" + userId + "] Request completed");
}

int main() {
    std::cout << "=== Logger Examples ===" << std::endl << std::endl;

    std::cout << "Example 1: Basic Console Logging\n";
    exampleBasicConsoleLogging();

    std::cout << "\nExample 2: File Logging\n";
    exampleFileLogging();

    std::cout << "\nExample 3: Multiple Loggers\n";
    exampleMultipleLoggers();

    std::cout << "\nExample 4: Stream-Style Logging\n";
    exampleStreamStyleLogging();

    std::cout << "\nExample 5: Multi-Target Logging\n";
    exampleMultiTargetLogging();

    std::cout << "\nExample 6: Log Level Filtering\n";
    exampleLogLevelFiltering();

    std::cout << "\nExample 7: Application Lifecycle\n";
    exampleApplicationLifecycle();

    std::cout << "\nExample 8: Error Tracking\n";
    exampleErrorTracking();

    std::cout << "\nExample 9: Performance Logging\n";
    examplePerformanceLogging();

    std::cout << "\nExample 10: Configuration Logging\n";
    exampleConfigurationLogging();

    std::cout << "\nExample 11: Request/Response Logging\n";
    exampleRequestResponseLogging();

    std::cout << "\nExample 12: Security Logging\n";
    exampleSecurityLogging();

    std::cout << "\nExample 13: Transaction Logging\n";
    exampleTransactionLogging();

    std::cout << "\nExample 14: Audit Logging\n";
    exampleAuditLogging();

    std::cout << "\nExample 15: Structured Logging\n";
    exampleStructuredLogging();

    // Clean up log files
    std::remove("app.log");
    std::remove("debug.log");
    std::remove("errors.log");
    std::remove("backup.log");
    std::remove("lifecycle.log");
    std::remove("perf.log");
    std::remove("http.log");
    std::remove("security.log");
    std::remove("transactions.log");
    std::remove("audit.log");

    return 0;
}
