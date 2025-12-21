#include "Logger.h"
#include <gtest/gtest.h>
#include <fstream>
#include <cstdio>

using namespace logging;

// ============================================================================
// Test Fixtures
// ============================================================================

class ConsoleLoggerTest : public ::testing::Test {
protected:
    std::unique_ptr<ConsoleLogger> logger;

    void SetUp() override {
        logger = std::make_unique<ConsoleLogger>("TestLogger", LogLevel::DEBUG);
    }

    void TearDown() override {
        logger.reset();
    }
};

class FileLoggerTest : public ::testing::Test {
protected:
    std::string log_filename = "test_log.txt";

    void SetUp() override {
        // Clean up any existing log file before each test
        std::remove(log_filename.c_str());
    }

    void TearDown() override {
        // Clean up log file after each test
        std::remove(log_filename.c_str());
    }
};

class MultiLoggerTest : public ::testing::Test {
protected:
    std::string filename1 = "multi1.txt";
    std::string filename2 = "multi2.txt";

    void SetUp() override {
        // Clean up any existing log files before each test
        std::remove(filename1.c_str());
        std::remove(filename2.c_str());
    }

    void TearDown() override {
        // Clean up log files after each test
        std::remove(filename1.c_str());
        std::remove(filename2.c_str());
    }
};

// ============================================================================
// Console Logger Tests
// ============================================================================

TEST_F(ConsoleLoggerTest, CreateLogger) {
    EXPECT_EQ(logger->getName(), "TestLogger");
}

TEST_F(ConsoleLoggerTest, GetLevel) {
    EXPECT_EQ(logger->getLevel(), LogLevel::DEBUG);
}

TEST_F(ConsoleLoggerTest, BasicLogging) {
    // These should not throw or crash
    EXPECT_NO_THROW(logger->debug("Debug message"));
    EXPECT_NO_THROW(logger->info("Info message"));
    EXPECT_NO_THROW(logger->warn("Warning message"));
    EXPECT_NO_THROW(logger->error("Error message"));
}

// ============================================================================
// File Logger Tests
// ============================================================================

TEST_F(FileLoggerTest, CreateFileLogger) {
    FileLogger logger("FileTest", log_filename, LogLevel::INFO, false);
    EXPECT_EQ(logger.getFilename(), log_filename);
}

TEST_F(FileLoggerTest, LogToFile) {
    {
        FileLogger logger("FileTest", log_filename, LogLevel::INFO, false);
        logger.info("Test message 1");
        logger.warn("Test message 2");
        logger.error("Test message 3");
    } // RAII: file should be closed here

    // Verify file was written
    std::ifstream file(log_filename);
    ASSERT_TRUE(file.good()) << "Log file should exist";

    std::string line;
    int lineCount = 0;
    while (std::getline(file, line)) {
        lineCount++;
    }

    EXPECT_EQ(lineCount, 3) << "Log file should have exactly 3 lines";
}

TEST_F(FileLoggerTest, LogLineContainsTimestamp) {
    {
        FileLogger logger("FileTest", log_filename, LogLevel::INFO, false);
        logger.info("Test message 1");
    }

    std::ifstream file(log_filename);
    ASSERT_TRUE(file.good());

    std::string line;
    std::getline(file, line);
    EXPECT_NE(line.find("[20"), std::string::npos) << "Log line should contain timestamp";
}

TEST_F(FileLoggerTest, LogLineContainsLevel) {
    {
        FileLogger logger("FileTest", log_filename, LogLevel::INFO, false);
        logger.info("Test info");
        logger.warn("Test warn");
        logger.error("Test error");
    }

    std::ifstream file(log_filename);
    ASSERT_TRUE(file.good());

    std::string line;
    int lineNum = 0;
    while (std::getline(file, line)) {
        lineNum++;
        // Each line should contain timestamp
        EXPECT_NE(line.find("[20"), std::string::npos)
            << "Line " << lineNum << " should contain timestamp: " << line;

        // Each line should contain log level
        bool hasLevel = line.find("[INFO ]") != std::string::npos ||
                       line.find("[WARN ]") != std::string::npos ||
                       line.find("[ERROR]") != std::string::npos;
        EXPECT_TRUE(hasLevel) << "Line " << lineNum << " should contain log level: " << line;
    }
}

// ============================================================================
// Log Level Filtering Tests
// ============================================================================

TEST_F(FileLoggerTest, LogLevelFiltering) {
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

    EXPECT_EQ(lineCount, 3) << "Only WARN, ERROR, and FATAL should be logged";

    file.close();
    std::remove(filename.c_str());
}

// ============================================================================
// Multi Logger Tests
// ============================================================================

TEST_F(MultiLoggerTest, CreateMultiLogger) {
    MultiLogger multi("MultiTest", LogLevel::INFO);
    EXPECT_EQ(multi.count(), 0) << "Multi logger should start with no destinations";
}

TEST_F(MultiLoggerTest, AddLoggers) {
    MultiLogger multi("MultiTest", LogLevel::INFO);

    multi.addLogger(std::make_unique<FileLogger>("File1", filename1, LogLevel::INFO, false));
    multi.addLogger(std::make_unique<FileLogger>("File2", filename2, LogLevel::INFO, false));
    multi.addLogger(std::make_unique<ConsoleLogger>("Console", LogLevel::INFO));

    EXPECT_EQ(multi.count(), 3) << "Multi logger should have 3 destinations";
}

TEST_F(MultiLoggerTest, LogToMultipleFiles) {
    {
        MultiLogger multi("MultiTest", LogLevel::INFO);

        multi.addLogger(std::make_unique<FileLogger>("File1", filename1, LogLevel::INFO, false));
        multi.addLogger(std::make_unique<FileLogger>("File2", filename2, LogLevel::INFO, false));

        multi.info("Test message");
        multi.error("Error message");
    }

    // Verify both files were written
    std::ifstream file1(filename1);
    std::ifstream file2(filename2);

    EXPECT_TRUE(file1.good()) << "Multi logger should write to file 1";
    EXPECT_TRUE(file2.good()) << "Multi logger should write to file 2";

    int count1 = 0, count2 = 0;
    std::string line;
    while (std::getline(file1, line)) count1++;
    while (std::getline(file2, line)) count2++;

    EXPECT_EQ(count1, 2) << "File 1 should have 2 lines";
    EXPECT_EQ(count2, 2) << "File 2 should have 2 lines";
    EXPECT_EQ(count1, count2) << "Both files should have same line count";
}

TEST_F(MultiLoggerTest, MultiLoggerWithConsole) {
    {
        MultiLogger multi("MultiTest", LogLevel::INFO);

        multi.addLogger(std::make_unique<FileLogger>("File1", filename1, LogLevel::INFO, false));
        multi.addLogger(std::make_unique<ConsoleLogger>("Console", LogLevel::INFO));

        EXPECT_NO_THROW(multi.info("Test message"));
        EXPECT_NO_THROW(multi.error("Error message"));
    }

    // Verify file was written
    std::ifstream file1(filename1);
    EXPECT_TRUE(file1.good()) << "Multi logger should write to file";

    int count = 0;
    std::string line;
    while (std::getline(file1, line)) count++;
    EXPECT_EQ(count, 2) << "File should have 2 lines";
}

// ============================================================================
// Stream-Style Logging Tests
// ============================================================================

TEST_F(FileLoggerTest, StreamStyleLogging) {
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

    EXPECT_EQ(lineCount, 3) << "Stream-style logging should write 3 lines";

    file.close();
    std::remove(filename.c_str());
}

TEST_F(FileLoggerTest, StreamStyleWithNumbers) {
    const std::string filename = "stream_numbers.txt";
    std::remove(filename.c_str());

    {
        FileLogger logger("StreamTest", filename, LogLevel::INFO, false);
        info(logger) << "Number: " << 42;
    }

    std::ifstream file(filename);
    ASSERT_TRUE(file.good());

    std::string line;
    std::getline(file, line);
    EXPECT_NE(line.find("42"), std::string::npos) << "Stream should log numbers correctly";

    file.close();
    std::remove(filename.c_str());
}

TEST_F(FileLoggerTest, StreamStyleWithFloats) {
    const std::string filename = "stream_floats.txt";
    std::remove(filename.c_str());

    {
        FileLogger logger("StreamTest", filename, LogLevel::INFO, false);
        info(logger) << "Pi: " << 3.14159;
    }

    std::ifstream file(filename);
    ASSERT_TRUE(file.good());

    std::string line;
    std::getline(file, line);
    EXPECT_NE(line.find("3.14"), std::string::npos) << "Stream should log floats correctly";

    file.close();
    std::remove(filename.c_str());
}

// ============================================================================
// Template Logging Tests
// ============================================================================

TEST_F(ConsoleLoggerTest, TemplateLoggingInteger) {
    EXPECT_NO_THROW(logger->log(LogLevel::INFO, 42));
}

TEST_F(ConsoleLoggerTest, TemplateLoggingDouble) {
    EXPECT_NO_THROW(logger->log(LogLevel::INFO, 3.14159));
}

TEST_F(ConsoleLoggerTest, TemplateLoggingString) {
    EXPECT_NO_THROW(logger->log(LogLevel::INFO, "String literal"));
}

TEST_F(ConsoleLoggerTest, TemplateLoggingBoolean) {
    EXPECT_NO_THROW(logger->log(LogLevel::INFO, true));
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
