// Phase 16-03: Console Application Testing - Command-line Args and File I/O
// Provides systematic testing for complete console applications
//
// Purpose: Verify transpiled code works correctly with:
// - Command-line argument handling (argc, argv)
// - File I/O operations (fopen, fread, fwrite, fclose)
// - Real-world console applications (file copy, wc, calculator, etc.)
//
// Test Coverage:
// - Command-line arguments (5 tests): argc counting, argv access, parsing, validation, multi-arg
// - File I/O operations (3 tests): write, read, append
// - Real-world applications (5 tests): file copy, line counter, word count, calculator, CSV parser
// - Total: 13 console application tests

#include <gtest/gtest.h>
#include "RuntimeTestHarness.h"
#include <filesystem>
#include <fstream>

// ConsoleAppTest: GTest fixture for console application tests
//
// Extends RuntimeIntegrationTest patterns to provide specialized helpers for:
// - Testing command-line argument handling
// - Testing file I/O operations
// - Testing complete real-world console applications
//
// Usage:
//   TEST_F(ConsoleAppTest, MyTest) {
//       assertConsoleAppRuns(code, {"arg1", "arg2"}, "expected output");
//   }
class ConsoleAppTest : public ::testing::Test {
protected:
    void SetUp() override {
        harness = std::make_unique<RuntimeTestHarness>();
    }

    void TearDown() override {
        harness.reset(); // Cleanup temp files
    }

    // Helper: Assert console app with args runs correctly
    void assertConsoleAppRuns(const std::string& code,
                             const std::vector<std::string>& args,
                             const std::string& expected_output = "") {
        auto result = harness->transpileCompileExecute(code, {}, args);
        ASSERT_TRUE(result.success)
            << "Execution failed:\n" << result.stderr_output;

        if (!expected_output.empty()) {
            EXPECT_EQ(result.stdout_output, expected_output)
                << "Output mismatch";
        }
    }

    // Helper: Create temporary test file
    std::string createTestFile(const std::string& content, const std::string& filename) {
        std::string file_path = harness->getTempDir() + "/" + filename;
        std::ofstream file(file_path);
        if (!file.is_open()) {
            return "";
        }
        file << content;
        file.close();
        return file_path;
    }

    // Helper: Read temporary test file
    std::string readTestFile(const std::string& file_path) {
        std::ifstream file(file_path);
        if (!file.is_open()) {
            return "";
        }
        std::stringstream buffer;
        buffer << file.rdbuf();
        return buffer.str();
    }

    std::unique_ptr<RuntimeTestHarness> harness;
};

// ============================================================================
// Task 2: Command-line Argument Tests (5 tests)
// ============================================================================

// Test 1: argc counting
TEST_F(ConsoleAppTest, CommandLineArgs_ArgcCounting) {
    const char* code = R"(
        #include <stdio.h>
        int main(int argc, char* argv[]) {
            printf("%d\n", argc);
            return 0;
        }
    )";

    // Test with 0 additional args (argc should be 1 for program name)
    auto result1 = harness->transpileCompileExecute(code, {}, {});
    ASSERT_TRUE(result1.success);
    EXPECT_EQ(result1.stdout_output, "1\n");

    // Test with 2 additional args (argc should be 3)
    auto result2 = harness->transpileCompileExecute(code, {}, {"arg1", "arg2"});
    ASSERT_TRUE(result2.success);
    EXPECT_EQ(result2.stdout_output, "3\n");
}

// Test 2: argv access
TEST_F(ConsoleAppTest, CommandLineArgs_ArgvAccess) {
    const char* code = R"(
        #include <stdio.h>
        int main(int argc, char* argv[]) {
            if (argc > 1) {
                printf("%s\n", argv[1]);
            }
            if (argc > 2) {
                printf("%s\n", argv[2]);
            }
            return 0;
        }
    )";

    assertConsoleAppRuns(code, {"hello", "world"}, "hello\nworld\n");
}

// Test 3: Argument parsing (convert string to int)
TEST_F(ConsoleAppTest, CommandLineArgs_ArgumentParsing) {
    const char* code = R"(
        #include <stdio.h>
        #include <stdlib.h>
        int main(int argc, char* argv[]) {
            if (argc != 3) {
                printf("usage: program <num1> <num2>\n");
                return 1;
            }
            int a = atoi(argv[1]);
            int b = atoi(argv[2]);
            printf("%d\n", a + b);
            return 0;
        }
    )";

    assertConsoleAppRuns(code, {"10", "20"}, "30\n");
}

// Test 4: Argument validation
TEST_F(ConsoleAppTest, CommandLineArgs_ArgumentValidation) {
    const char* code = R"(
        #include <stdio.h>
        #include <string.h>
        int main(int argc, char* argv[]) {
            if (argc < 2) {
                printf("error: missing argument\n");
                return 1;
            }

            if (strcmp(argv[1], "--help") == 0) {
                printf("help: this is a help message\n");
                return 0;
            }

            printf("argument: %s\n", argv[1]);
            return 0;
        }
    )";

    // Test with --help flag
    assertConsoleAppRuns(code, {"--help"}, "help: this is a help message\n");

    // Test with normal argument
    assertConsoleAppRuns(code, {"test"}, "argument: test\n");
}

// Test 5: Multiple arguments with options
TEST_F(ConsoleAppTest, CommandLineArgs_MultipleArguments) {
    const char* code = R"(
        #include <stdio.h>
        #include <string.h>
        int main(int argc, char* argv[]) {
            int verbose = 0;
            int count = 0;

            for (int i = 1; i < argc; i++) {
                if (strcmp(argv[i], "-v") == 0) {
                    verbose = 1;
                } else {
                    count++;
                }
            }

            if (verbose) {
                printf("verbose mode enabled\n");
            }
            printf("non-option arguments: %d\n", count);
            return 0;
        }
    )";

    assertConsoleAppRuns(code, {"-v", "file1", "file2"}, "verbose mode enabled\nnon-option arguments: 2\n");
}

// ============================================================================
// Task 3.1: File I/O Tests (3 tests)
// ============================================================================

// Test 6: File write operation
TEST_F(ConsoleAppTest, FileIO_WriteOperation) {
    const char* code_template = R"(
        #include <stdio.h>
        int main() {
            FILE* f = fopen("%s", "w");
            if (!f) {
                printf("error: cannot open file\n");
                return 1;
            }
            fprintf(f, "Hello, File I/O!\n");
            fclose(f);
            printf("success\n");
            return 0;
        }
    )";

    std::string output_file = harness->getTempDir() + "/test_write.txt";
    char code[512];
    snprintf(code, sizeof(code), code_template, output_file.c_str());

    assertConsoleAppRuns(code, {}, "success\n");

    // Verify file was written
    std::string content = readTestFile(output_file);
    EXPECT_EQ(content, "Hello, File I/O!\n");
}

// Test 7: File read operation
TEST_F(ConsoleAppTest, FileIO_ReadOperation) {
    // Create test input file
    std::string input_file = createTestFile("Line 1\nLine 2\nLine 3\n", "test_read.txt");
    ASSERT_FALSE(input_file.empty());

    const char* code_template = R"(
        #include <stdio.h>
        int main() {
            FILE* f = fopen("%s", "r");
            if (!f) {
                printf("error: cannot open file\n");
                return 1;
            }
            char line[256];
            int count = 0;
            while (fgets(line, sizeof(line), f)) {
                count++;
            }
            fclose(f);
            printf("lines: %%d\n", count);
            return 0;
        }
    )";

    char code[512];
    snprintf(code, sizeof(code), code_template, input_file.c_str());

    assertConsoleAppRuns(code, {}, "lines: 3\n");
}

// Test 8: File append operation
TEST_F(ConsoleAppTest, FileIO_AppendOperation) {
    // Create initial file
    std::string file_path = createTestFile("Initial content\n", "test_append.txt");
    ASSERT_FALSE(file_path.empty());

    const char* code_template = R"(
        #include <stdio.h>
        int main() {
            FILE* f = fopen("%s", "a");
            if (!f) {
                printf("error: cannot open file\n");
                return 1;
            }
            fprintf(f, "Appended content\n");
            fclose(f);
            printf("success\n");
            return 0;
        }
    )";

    char code[512];
    snprintf(code, sizeof(code), code_template, file_path.c_str());

    assertConsoleAppRuns(code, {}, "success\n");

    // Verify file has both contents
    std::string content = readTestFile(file_path);
    EXPECT_EQ(content, "Initial content\nAppended content\n");
}

// ============================================================================
// Task 3.2: Real-world Application Tests (5 tests)
// ============================================================================

// Test 9: File copy utility
TEST_F(ConsoleAppTest, RealWorld_FileCopyUtility) {
    // Create source file
    std::string src_file = createTestFile("This is test content\nWith multiple lines\n", "copy_source.txt");
    ASSERT_FALSE(src_file.empty());

    std::string dst_file = harness->getTempDir() + "/copy_dest.txt";

    const char* code_template = R"(
        #include <stdio.h>
        int main(int argc, char* argv[]) {
            if (argc != 3) {
                printf("usage: copy <source> <dest>\n");
                return 1;
            }

            FILE* src = fopen(argv[1], "r");
            if (!src) {
                printf("error: cannot open source\n");
                return 1;
            }

            FILE* dst = fopen(argv[2], "w");
            if (!dst) {
                fclose(src);
                printf("error: cannot open dest\n");
                return 1;
            }

            char buffer[4096];
            size_t bytes;
            while ((bytes = fread(buffer, 1, sizeof(buffer), src)) > 0) {
                fwrite(buffer, 1, bytes, dst);
            }

            fclose(src);
            fclose(dst);
            printf("copied\n");
            return 0;
        }
    )";

    assertConsoleAppRuns(code_template, {src_file, dst_file}, "copied\n");

    // Verify destination file content
    std::string content = readTestFile(dst_file);
    EXPECT_EQ(content, "This is test content\nWith multiple lines\n");
}

// Test 10: Line counter (wc -l clone)
TEST_F(ConsoleAppTest, RealWorld_LineCounter) {
    // Create test file
    std::string test_file = createTestFile("Line 1\nLine 2\nLine 3\nLine 4\nLine 5\n", "linecount.txt");
    ASSERT_FALSE(test_file.empty());

    const char* code_template = R"(
        #include <stdio.h>
        int main(int argc, char* argv[]) {
            if (argc != 2) {
                printf("usage: linecount <file>\n");
                return 1;
            }

            FILE* f = fopen(argv[1], "r");
            if (!f) {
                printf("error: cannot open file\n");
                return 1;
            }

            int lines = 0;
            int ch;
            while ((ch = fgetc(f)) != EOF) {
                if (ch == '\n') {
                    lines++;
                }
            }

            fclose(f);
            printf("%d\n", lines);
            return 0;
        }
    )";

    assertConsoleAppRuns(code_template, {test_file}, "5\n");
}

// Test 11: Word counter (wc -w clone)
TEST_F(ConsoleAppTest, RealWorld_WordCounter) {
    // Create test file
    std::string test_file = createTestFile("hello world\nthis is a test\n", "wordcount.txt");
    ASSERT_FALSE(test_file.empty());

    const char* code_template = R"(
        #include <stdio.h>
        #include <ctype.h>
        int main(int argc, char* argv[]) {
            if (argc != 2) {
                printf("usage: wordcount <file>\n");
                return 1;
            }

            FILE* f = fopen(argv[1], "r");
            if (!f) {
                printf("error: cannot open file\n");
                return 1;
            }

            int words = 0;
            int in_word = 0;
            int ch;

            while ((ch = fgetc(f)) != EOF) {
                if (isspace(ch)) {
                    in_word = 0;
                } else if (!in_word) {
                    in_word = 1;
                    words++;
                }
            }

            fclose(f);
            printf("%d\n", words);
            return 0;
        }
    )";

    assertConsoleAppRuns(code_template, {test_file}, "6\n");
}

// Test 12: Simple calculator
TEST_F(ConsoleAppTest, RealWorld_SimpleCalculator) {
    const char* code = R"(
        #include <stdio.h>
        #include <stdlib.h>
        #include <string.h>

        int main(int argc, char* argv[]) {
            if (argc != 4) {
                printf("usage: calc <num1> <op> <num2>\n");
                return 1;
            }

            double a = atof(argv[1]);
            char* op = argv[2];
            double b = atof(argv[3]);
            double result;

            if (strcmp(op, "+") == 0) {
                result = a + b;
            } else if (strcmp(op, "-") == 0) {
                result = a - b;
            } else if (strcmp(op, "*") == 0) {
                result = a * b;
            } else if (strcmp(op, "/") == 0) {
                if (b == 0) {
                    printf("error: division by zero\n");
                    return 1;
                }
                result = a / b;
            } else {
                printf("error: unknown operator\n");
                return 1;
            }

            printf("%.2f\n", result);
            return 0;
        }
    )";

    // Test various operations
    assertConsoleAppRuns(code, {"10", "+", "5"}, "15.00\n");
    assertConsoleAppRuns(code, {"20", "-", "8"}, "12.00\n");
    assertConsoleAppRuns(code, {"6", "*", "7"}, "42.00\n");
    assertConsoleAppRuns(code, {"100", "/", "4"}, "25.00\n");
}

// Test 13: Simple CSV parser
TEST_F(ConsoleAppTest, RealWorld_CSVParser) {
    // Create CSV test file
    std::string csv_file = createTestFile("Name,Age,City\nAlice,30,NYC\nBob,25,LA\nCharlie,35,SF\n", "test.csv");
    ASSERT_FALSE(csv_file.empty());

    const char* code_template = R"(
        #include <stdio.h>
        #include <string.h>

        int main(int argc, char* argv[]) {
            if (argc != 2) {
                printf("usage: csvparse <file>\n");
                return 1;
            }

            FILE* f = fopen(argv[1], "r");
            if (!f) {
                printf("error: cannot open file\n");
                return 1;
            }

            char line[256];
            int row_count = 0;

            // Skip header
            if (fgets(line, sizeof(line), f)) {
                row_count++;
            }

            // Count data rows
            int data_rows = 0;
            while (fgets(line, sizeof(line), f)) {
                data_rows++;
            }

            fclose(f);
            printf("header: 1\ndata rows: %d\ntotal: %d\n", data_rows, row_count + data_rows);
            return 0;
        }
    )";

    assertConsoleAppRuns(code_template, {csv_file}, "header: 1\ndata rows: 3\ntotal: 4\n");
}
