// Phase 16-03: Console Application End-to-End Tests
// Tests complete console programs with command-line args, file I/O, stdin/stdout
//
// Purpose: Verify that transpiled C code works correctly in real-world scenarios
// - Command-line argument handling (argc, argv)
// - File I/O operations (reading/writing files)
// - Standard input/output (stdin, stdout, stderr)
// - Exit codes (error handling, return codes)
//
// Test Coverage:
// - Command-line args (5 tests): NoArguments, SingleArgument, MultipleArguments,
//   InvalidArgumentHandling, NumericArgumentParsing
// - File I/O (3 tests): FileCopy, LineCounter, FileNotFoundError
// - Real-world apps (5 tests): WordCount, SimpleCalculator, CSVParser,
//   TextFilter, ConfigGenerator

#include <gtest/gtest.h>
#include "RuntimeTestHarness.h"
#include <fstream>
#include <sstream>
#include <memory>

// ConsoleAppTest: GTest fixture for console application testing
//
// Provides helper methods for:
// - Creating test input files
// - Reading output files
// - Testing console apps with arguments
// - Testing console apps with stdin
//
// Usage:
//   TEST_F(ConsoleAppTest, MyTest) {
//       assertConsoleAppWorks(code, {"arg1", "arg2"}, "expected output\n");
//   }
class ConsoleAppTest : public ::testing::Test {
protected:
    void SetUp() override {
        harness = std::make_unique<RuntimeTestHarness>();
    }

    void TearDown() override {
        harness.reset(); // Cleanup temp files
    }

    // Helper: Create test input file
    std::string createInputFile(const std::string& content) {
        return harness->createTempFile(content, ".txt");
    }

    // Helper: Read output file
    std::string readOutputFile(const std::string& path) {
        std::ifstream file(path);
        if (!file.is_open()) {
            return "";
        }
        return std::string(std::istreambuf_iterator<char>(file),
                          std::istreambuf_iterator<char>());
    }

    // Helper: Test console app with args
    void assertConsoleAppWorks(
        const std::string& cpp_code,
        const std::vector<std::string>& args,
        const std::string& expected_stdout = "",
        int expected_exit_code = 0) {

        auto result = harness->transpileCompileExecute(cpp_code, {}, args);

        EXPECT_EQ(result.exit_code, expected_exit_code)
            << "Exit code mismatch";

        if (!expected_stdout.empty()) {
            EXPECT_EQ(result.stdout_output, expected_stdout)
                << "Output mismatch";
        }

        ASSERT_TRUE(result.success || expected_exit_code != 0)
            << "Execution failed:\n" << result.stderr_output;
    }

    // Helper: Test app with stdin
    void assertConsoleAppWithStdin(
        const std::string& cpp_code,
        const std::string& stdin_data,
        const std::string& expected_stdout,
        int expected_exit_code = 0) {

        auto result = harness->transpileCompileExecute(cpp_code, {}, {}, stdin_data);

        EXPECT_EQ(result.exit_code, expected_exit_code);
        EXPECT_EQ(result.stdout_output, expected_stdout);
    }

    std::unique_ptr<RuntimeTestHarness> harness;
};

// ============================================================================
// Command-Line Argument Tests (5 tests)
// ============================================================================

TEST_F(ConsoleAppTest, NoArguments) {
    const char* code = R"(
        #include <stdio.h>
        int main(int argc, char* argv[]) {
            printf("argc=%d\n", argc);
            return 0;
        }
    )";
    assertConsoleAppWorks(code, {}, "argc=1\n", 0);
}

TEST_F(ConsoleAppTest, SingleArgument) {
    const char* code = R"(
        #include <stdio.h>
        int main(int argc, char* argv[]) {
            if (argc > 1) {
                printf("arg1=%s\n", argv[1]);
            }
            return 0;
        }
    )";
    assertConsoleAppWorks(code, {"hello"}, "arg1=hello\n", 0);
}

TEST_F(ConsoleAppTest, MultipleArguments) {
    const char* code = R"(
        #include <stdio.h>
        int main(int argc, char* argv[]) {
            for (int i = 1; i < argc; i++) {
                printf("%s ", argv[i]);
            }
            printf("\n");
            return 0;
        }
    )";
    assertConsoleAppWorks(code, {"one", "two", "three"}, "one two three \n", 0);
}

TEST_F(ConsoleAppTest, InvalidArgumentHandling) {
    const char* code = R"(
        #include <stdio.h>
        #include <stdlib.h>
        int main(int argc, char* argv[]) {
            if (argc < 2) {
                fprintf(stderr, "Error: missing argument\n");
                return 1;
            }
            printf("arg=%s\n", argv[1]);
            return 0;
        }
    )";
    auto result = harness->transpileCompileExecute(code, {}, {});
    EXPECT_EQ(result.exit_code, 1);
    EXPECT_NE(result.stderr_output.find("Error: missing argument"), std::string::npos);
}

TEST_F(ConsoleAppTest, NumericArgumentParsing) {
    const char* code = R"(
        #include <stdio.h>
        #include <stdlib.h>
        int main(int argc, char* argv[]) {
            if (argc != 3) return 1;
            int a = atoi(argv[1]);
            int b = atoi(argv[2]);
            printf("%d\n", a + b);
            return 0;
        }
    )";
    assertConsoleAppWorks(code, {"10", "32"}, "42\n", 0);
}

// ============================================================================
// File I/O Tests (3 tests)
// ============================================================================

TEST_F(ConsoleAppTest, FileCopy) {
    const char* code = R"(
        #include <stdio.h>
        int main(int argc, char* argv[]) {
            if (argc != 3) return 1;

            FILE* in = fopen(argv[1], "r");
            FILE* out = fopen(argv[2], "w");

            if (!in || !out) return 2;

            char buf[1024];
            while (fgets(buf, sizeof(buf), in)) {
                fputs(buf, out);
            }

            fclose(in);
            fclose(out);
            printf("Copied successfully\n");
            return 0;
        }
    )";

    std::string input = createInputFile("line1\nline2\nline3\n");
    std::string output = harness->getTempPath("output.txt");

    assertConsoleAppWorks(code, {input, output}, "Copied successfully\n", 0);

    std::string result = readOutputFile(output);
    EXPECT_EQ(result, "line1\nline2\nline3\n");
}

TEST_F(ConsoleAppTest, LineCounter) {
    const char* code = R"(
        #include <stdio.h>
        int main(int argc, char* argv[]) {
            if (argc != 2) return 1;
            FILE* f = fopen(argv[1], "r");
            if (!f) return 2;

            int lines = 0;
            char buf[1024];
            while (fgets(buf, sizeof(buf), f)) {
                lines++;
            }
            fclose(f);

            printf("Lines: %d\n", lines);
            return 0;
        }
    )";

    std::string input = createInputFile("a\nb\nc\nd\ne\n");
    assertConsoleAppWorks(code, {input}, "Lines: 5\n", 0);
}

TEST_F(ConsoleAppTest, FileNotFoundError) {
    const char* code = R"(
        #include <stdio.h>
        int main(int argc, char* argv[]) {
            if (argc != 2) return 1;
            FILE* f = fopen(argv[1], "r");
            if (!f) {
                fprintf(stderr, "Error: file not found\n");
                return 2;
            }
            fclose(f);
            printf("File opened\n");
            return 0;
        }
    )";

    auto result = harness->transpileCompileExecute(code, {}, {"/nonexistent/file.txt"});
    EXPECT_EQ(result.exit_code, 2);
    EXPECT_NE(result.stderr_output.find("Error: file not found"), std::string::npos);
}

// ============================================================================
// Real-World Application Tests (5 tests)
// ============================================================================

TEST_F(ConsoleAppTest, WordCount) {
    // wc-like utility: count lines, words, characters
    const char* code = R"(
        #include <stdio.h>
        #include <ctype.h>
        int main(int argc, char* argv[]) {
            if (argc != 2) return 1;
            FILE* f = fopen(argv[1], "r");
            if (!f) return 2;

            int lines = 0, words = 0, chars = 0;
            int in_word = 0;
            int c;

            while ((c = fgetc(f)) != EOF) {
                chars++;
                if (c == '\n') lines++;
                if (isspace(c)) {
                    in_word = 0;
                } else if (!in_word) {
                    in_word = 1;
                    words++;
                }
            }

            fclose(f);
            printf("%d %d %d\n", lines, words, chars);
            return 0;
        }
    )";

    std::string input = createInputFile("hello world\ntest file\n");
    // 2 lines, 4 words, 22 chars (12 + 1 newline + 9 chars = 22)
    assertConsoleAppWorks(code, {input}, "2 4 22\n", 0);
}

TEST_F(ConsoleAppTest, SimpleCalculator) {
    // Calculator: ./calc add 10 20 → 30
    const char* code = R"(
        #include <stdio.h>
        #include <stdlib.h>
        #include <string.h>
        int main(int argc, char* argv[]) {
            if (argc != 4) return 1;

            char* op = argv[1];
            int a = atoi(argv[2]);
            int b = atoi(argv[3]);
            int result = 0;

            if (strcmp(op, "add") == 0) {
                result = a + b;
            } else if (strcmp(op, "sub") == 0) {
                result = a - b;
            } else if (strcmp(op, "mul") == 0) {
                result = a * b;
            } else if (strcmp(op, "div") == 0) {
                if (b == 0) {
                    fprintf(stderr, "Error: division by zero\n");
                    return 2;
                }
                result = a / b;
            } else {
                fprintf(stderr, "Error: unknown operation\n");
                return 3;
            }

            printf("%d\n", result);
            return 0;
        }
    )";

    assertConsoleAppWorks(code, {"add", "10", "32"}, "42\n", 0);
    assertConsoleAppWorks(code, {"sub", "50", "8"}, "42\n", 0);
    assertConsoleAppWorks(code, {"mul", "6", "7"}, "42\n", 0);
    assertConsoleAppWorks(code, {"div", "84", "2"}, "42\n", 0);
}

TEST_F(ConsoleAppTest, CSVParser) {
    // Parse CSV, compute sum/average
    const char* code = R"(
        #include <stdio.h>
        #include <stdlib.h>
        #include <string.h>
        int main(int argc, char* argv[]) {
            if (argc != 2) return 1;
            FILE* f = fopen(argv[1], "r");
            if (!f) return 2;

            int sum = 0;
            int count = 0;
            char line[1024];

            // Skip header
            fgets(line, sizeof(line), f);

            // Parse data rows
            while (fgets(line, sizeof(line), f)) {
                char* token = strtok(line, ",");
                if (token) {
                    int value = atoi(token);
                    sum += value;
                    count++;
                }
            }

            fclose(f);

            if (count > 0) {
                int avg = sum / count;
                printf("sum=%d avg=%d\n", sum, avg);
            }

            return 0;
        }
    )";

    std::string input = createInputFile("value\n10\n20\n30\n40\n");
    assertConsoleAppWorks(code, {input}, "sum=100 avg=25\n", 0);
}

TEST_F(ConsoleAppTest, TextFilter) {
    // Read stdin, filter lines matching pattern, write stdout
    const char* code = R"(
        #include <stdio.h>
        #include <string.h>
        int main(int argc, char* argv[]) {
            if (argc != 2) return 1;

            char* pattern = argv[1];
            char line[1024];

            while (fgets(line, sizeof(line), stdin)) {
                if (strstr(line, pattern)) {
                    printf("%s", line);
                }
            }

            return 0;
        }
    )";

    std::string stdin_input = "apple\nbanana\napple pie\ncherry\napricot\n";
    std::string expected = "apple\napple pie\napricot\n";

    auto result = harness->transpileCompileExecute(code, {}, {"ap"}, stdin_input);
    EXPECT_EQ(result.exit_code, 0);
    EXPECT_EQ(result.stdout_output, expected);
}

TEST_F(ConsoleAppTest, ConfigGenerator) {
    // Generate config file from template + args
    const char* code = R"(
        #include <stdio.h>
        #include <string.h>
        int main(int argc, char* argv[]) {
            if (argc != 4) {
                fprintf(stderr, "Usage: config <name> <port> <output>\n");
                return 1;
            }

            char* name = argv[1];
            char* port = argv[2];
            char* output_file = argv[3];

            FILE* f = fopen(output_file, "w");
            if (!f) {
                fprintf(stderr, "Error: cannot create output file\n");
                return 2;
            }

            fprintf(f, "[server]\n");
            fprintf(f, "name=%s\n", name);
            fprintf(f, "port=%s\n", port);
            fprintf(f, "enabled=true\n");

            fclose(f);
            printf("Config generated: %s\n", output_file);
            return 0;
        }
    )";

    std::string output = harness->getTempPath("config.ini");
    assertConsoleAppWorks(code, {"myserver", "8080", output}, "Config generated: " + output + "\n", 0);

    std::string config = readOutputFile(output);
    EXPECT_NE(config.find("[server]"), std::string::npos);
    EXPECT_NE(config.find("name=myserver"), std::string::npos);
    EXPECT_NE(config.find("port=8080"), std::string::npos);
    EXPECT_NE(config.find("enabled=true"), std::string::npos);
}
