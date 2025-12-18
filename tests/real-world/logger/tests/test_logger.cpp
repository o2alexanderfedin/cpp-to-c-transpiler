#include "Logger.h"
#include <iostream>
#include <fstream>
#include <cassert>
#include <cstdio>

using namespace logging;

void test(const std::string& name, bool condition) {
    if (condition) {
        std::cout << "[PASS] " << name << std::endl;
    } else {
        std::cout << "[FAIL] " << name << std::endl;
        throw std::runtime_error("Test failed: " + name);
    }
}

void testConsoleLogger() {
    ConsoleLogger logger("TestLogger", LogLevel::DEBUG);

    test("Console logger created", logger.getName() == "TestLogger");
    test("Console logger level", logger.getLevel() == LogLevel::DEBUG);

    logger.debug("Debug message");
    logger.info("Info message");
    logger.warn("Warning message");
    logger.error("Error message");

    test("Console logger basic logging", true);
}

void testFileLogger() {
    const std::string filename = "test_log.txt";

    // Remove old log file
    std::remove(filename.c_str());

    {
        FileLogger logger("FileTest", filename, LogLevel::INFO, false);

        logger.info("Test message 1");
        logger.warn("Test message 2");
        logger.error("Test message 3");

        test("File logger created", logger.getFilename() == filename);
    } // RAII: file should be closed here

    // Verify file was written
    std::ifstream file(filename);
    test("Log file exists", file.good());

    std::string line;
    int lineCount = 0;
    while (std::getline(file, line)) {
        lineCount++;
        test("Log line contains timestamp", line.find("[20") != std::string::npos);
        test("Log line contains level", line.find("[INFO]") != std::string::npos ||
                                       line.find("[WARN]") != std::string::npos ||
                                       line.find("[ERROR]") != std::string::npos);
    }

    test("Log file has correct number of lines", lineCount == 3);

    file.close();
    std::remove(filename.c_str());
}

void testLogLevels() {
    const std::string filename = "test_levels.txt";
    std::remove(filename.c_str());

    {
        FileLogger logger("LevelTest", filename, LogLevel::WARN, false);

        logger.debug("Should not appear");  // Below threshold
        logger.info("Should not appear");   // Below threshold
        logger.warn("Should appear");       // At threshold
        logger.error("Should appear");      // Above threshold
        logger.fatal("Should appear");      // Above threshold
    }

    // Verify only 3 messages were written
    std::ifstream file(filename);
    int lineCount = 0;
    std::string line;
    while (std::getline(file, line)) {
        lineCount++;
    }

    test("Log level filtering works", lineCount == 3);

    file.close();
    std::remove(filename.c_str());
}

void testMultiLogger() {
    const std::string filename1 = "multi1.txt";
    const std::string filename2 = "multi2.txt";

    std::remove(filename1.c_str());
    std::remove(filename2.c_str());

    {
        MultiLogger multi("MultiTest", LogLevel::INFO);

        multi.addLogger(std::make_unique<FileLogger>("File1", filename1, LogLevel::INFO, false));
        multi.addLogger(std::make_unique<FileLogger>("File2", filename2, LogLevel::INFO, false));
        multi.addLogger(std::make_unique<ConsoleLogger>("Console", LogLevel::INFO));

        test("Multi logger has 3 destinations", multi.count() == 3);

        multi.info("Test message");
        multi.error("Error message");
    }

    // Verify both files were written
    std::ifstream file1(filename1);
    std::ifstream file2(filename2);

    test("Multi logger wrote to file 1", file1.good());
    test("Multi logger wrote to file 2", file2.good());

    int count1 = 0, count2 = 0;
    std::string line;
    while (std::getline(file1, line)) count1++;
    while (std::getline(file2, line)) count2++;

    test("Both files have same line count", count1 == count2 && count1 == 2);

    file1.close();
    file2.close();
    std::remove(filename1.c_str());
    std::remove(filename2.c_str());
}

void testStreamStyle() {
    const std::string filename = "stream_test.txt";
    std::remove(filename.c_str());

    {
        FileLogger logger("StreamTest", filename, LogLevel::INFO, false);

        // Stream-style logging
        info(logger) << "Message " << 1 << ": " << 3.14;
        warn(logger) << "Warning: " << "test";
        error(logger) << "Error code: " << 42;
    }

    std::ifstream file(filename);
    int lineCount = 0;
    std::string line;
    while (std::getline(file, line)) {
        lineCount++;
    }

    test("Stream-style logging works", lineCount == 3);

    file.close();
    std::remove(filename.c_str());
}

void testTemplateLogging() {
    ConsoleLogger logger("TemplateTest", LogLevel::INFO);

    // Test template log method with different types
    logger.log(LogLevel::INFO, 42);
    logger.log(LogLevel::INFO, 3.14159);
    logger.log(LogLevel::INFO, "String literal");
    logger.log(LogLevel::INFO, true);

    test("Template logging compiles and runs", true);
}

int main() {
    try {
        std::cout << "=== Logger Tests ===" << std::endl;

        testConsoleLogger();
        testFileLogger();
        testLogLevels();
        testMultiLogger();
        testStreamStyle();
        testTemplateLogging();

        std::cout << "\n=== All tests passed! ===" << std::endl;
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Test failed with exception: " << e.what() << std::endl;
        return 1;
    }
}
