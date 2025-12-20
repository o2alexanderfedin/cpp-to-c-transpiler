# Logger - Real-World Test Project

## Overview
A multi-level logging system demonstrating:
- RAII for file handle management
- Templates for type-safe formatting
- Inheritance hierarchy (Logger -> FileLogger, ConsoleLogger)
- Operator overloading (<<)
- Singleton pattern
- Thread-local storage

## Target Size
1,000-1,500 lines of code

## C++ Features Tested
1. **Classes & Inheritance**: Logger base class, FileLogger, ConsoleLogger
2. **RAII**: Automatic file handle closure
3. **Templates**: Generic log formatting
4. **Operator Overloading**: Stream-style logging (log << "message")
5. **Singleton**: Global logger instance
6. **Virtual Functions**: Polymorphic write methods
7. **STL**: std::string, std::fstream, std::ostringstream

## Validation Criteria
1. Compiles successfully to C
2. Logs messages at different levels (DEBUG, INFO, WARN, ERROR)
3. File logger creates and writes to files correctly
4. Console logger outputs to stdout/stderr
5. RAII ensures file handles closed properly
6. Performance within 20% of native C++
