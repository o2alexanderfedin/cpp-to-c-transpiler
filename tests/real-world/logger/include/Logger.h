#ifndef LOGGER_H
#define LOGGER_H

#include <string>
#include <fstream>
#include <sstream>
#include <memory>
#include <ctime>
#include <iostream>

namespace logging {

// Log levels
enum class LogLevel {
    DEBUG = 0,
    INFO = 1,
    WARN = 2,
    ERROR = 3,
    FATAL = 4
};

// Convert log level to string
inline const char* levelToString(LogLevel level) {
    switch (level) {
        case LogLevel::DEBUG: return "DEBUG";
        case LogLevel::INFO:  return "INFO ";
        case LogLevel::WARN:  return "WARN ";
        case LogLevel::ERROR: return "ERROR";
        case LogLevel::FATAL: return "FATAL";
        default: return "UNKNOWN";
    }
}

// Base Logger class (abstract)
class Logger {
protected:
    LogLevel minLevel_;
    std::string name_;

    // Format timestamp
    std::string getTimestamp() const {
        std::time_t now = std::time(nullptr);
        char buf[32];
        std::strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S", std::localtime(&now));
        return std::string(buf);
    }

    // Format log message
    std::string formatMessage(LogLevel level, const std::string& message) const {
        std::ostringstream oss;
        oss << "[" << getTimestamp() << "] "
            << "[" << levelToString(level) << "] "
            << "[" << name_ << "] "
            << message;
        return oss.str();
    }

public:
    explicit Logger(const std::string& name, LogLevel minLevel = LogLevel::INFO)
        : minLevel_(minLevel), name_(name) {}

    virtual ~Logger() = default;

    // Pure virtual write method
    virtual void write(LogLevel level, const std::string& message) = 0;

    // Convenience methods
    void debug(const std::string& message) {
        if (minLevel_ <= LogLevel::DEBUG) {
            write(LogLevel::DEBUG, message);
        }
    }

    void info(const std::string& message) {
        if (minLevel_ <= LogLevel::INFO) {
            write(LogLevel::INFO, message);
        }
    }

    void warn(const std::string& message) {
        if (minLevel_ <= LogLevel::WARN) {
            write(LogLevel::WARN, message);
        }
    }

    void error(const std::string& message) {
        if (minLevel_ <= LogLevel::ERROR) {
            write(LogLevel::ERROR, message);
        }
    }

    void fatal(const std::string& message) {
        write(LogLevel::FATAL, message);
    }

    // Template method for any type convertible to string
    template<typename T>
    void log(LogLevel level, const T& message) {
        std::ostringstream oss;
        oss << message;
        write(level, oss.str());
    }

    void setLevel(LogLevel level) { minLevel_ = level; }
    LogLevel getLevel() const { return minLevel_; }
    const std::string& getName() const { return name_; }
};

// Console Logger
class ConsoleLogger : public Logger {
private:
    bool useStderr_;

public:
    explicit ConsoleLogger(const std::string& name,
                          LogLevel minLevel = LogLevel::INFO,
                          bool useStderr = false)
        : Logger(name, minLevel), useStderr_(useStderr) {}

    void write(LogLevel level, const std::string& message) override {
        std::string formatted = formatMessage(level, message);

        if (useStderr_ || level >= LogLevel::ERROR) {
            std::cerr << formatted << std::endl;
        } else {
            std::cout << formatted << std::endl;
        }
    }
};

// File Logger with RAII
class FileLogger : public Logger {
private:
    std::string filename_;
    std::ofstream file_;
    bool append_;

public:
    explicit FileLogger(const std::string& name,
                       const std::string& filename,
                       LogLevel minLevel = LogLevel::INFO,
                       bool append = true)
        : Logger(name, minLevel), filename_(filename), append_(append) {

        std::ios_base::openmode mode = std::ios_base::out;
        if (append) {
            mode |= std::ios_base::app;
        } else {
            mode |= std::ios_base::trunc;
        }

        file_.open(filename, mode);
        if (!file_.is_open()) {
            throw std::runtime_error("Failed to open log file: " + filename);
        }
    }

    ~FileLogger() override {
        if (file_.is_open()) {
            file_.close();
        }
    }

    // Delete copy/move (file handle is unique)
    FileLogger(const FileLogger&) = delete;
    FileLogger& operator=(const FileLogger&) = delete;
    FileLogger(FileLogger&&) = delete;
    FileLogger& operator=(FileLogger&&) = delete;

    void write(LogLevel level, const std::string& message) override {
        if (file_.is_open()) {
            file_ << formatMessage(level, message) << std::endl;
            file_.flush();  // Ensure immediate write
        }
    }

    const std::string& getFilename() const { return filename_; }
};

// Multi-target logger (logs to multiple destinations)
class MultiLogger : public Logger {
private:
    std::vector<std::unique_ptr<Logger>> loggers_;

public:
    explicit MultiLogger(const std::string& name, LogLevel minLevel = LogLevel::INFO)
        : Logger(name, minLevel) {}

    void addLogger(std::unique_ptr<Logger> logger) {
        loggers_.push_back(std::move(logger));
    }

    void write(LogLevel level, const std::string& message) override {
        for (auto& logger : loggers_) {
            logger->write(level, message);
        }
    }

    size_t count() const { return loggers_.size(); }
};

// Stream-style log entry helper
class LogStream {
private:
    Logger& logger_;
    LogLevel level_;
    std::ostringstream stream_;

public:
    LogStream(Logger& logger, LogLevel level)
        : logger_(logger), level_(level) {}

    ~LogStream() {
        logger_.write(level_, stream_.str());
    }

    template<typename T>
    LogStream& operator<<(const T& value) {
        stream_ << value;
        return *this;
    }
};

// Helper functions for stream-style logging
inline LogStream debug(Logger& logger) {
    return LogStream(logger, LogLevel::DEBUG);
}

inline LogStream info(Logger& logger) {
    return LogStream(logger, LogLevel::INFO);
}

inline LogStream warn(Logger& logger) {
    return LogStream(logger, LogLevel::WARN);
}

inline LogStream error(Logger& logger) {
    return LogStream(logger, LogLevel::ERROR);
}

inline LogStream fatal(Logger& logger) {
    return LogStream(logger, LogLevel::FATAL);
}

} // namespace logging

#endif // LOGGER_H
