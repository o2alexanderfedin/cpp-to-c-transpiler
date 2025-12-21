#!/usr/bin/env python3
"""
Script to migrate integration tests from custom test framework to Google Test.

Converts:
- TEST_START/TEST_PASS/TEST_FAIL macros to GTest TEST() or TEST_F()
- ASSERT macros to EXPECT_TRUE, EXPECT_EQ, etc.
- main() with test runner to GTest main
"""

import re
import sys
from pathlib import Path

def migrate_test_file(file_path):
    """Migrate a single test file to GTest format."""
    with open(file_path, 'r') as f:
        content = f.read()

    # Store original header comments
    header_match = re.match(r'(//[^\n]*\n)+', content)
    header = header_match.group(0) if header_match else ""

    # Add GTest migration note to header
    if "Google Test" not in header:
        header += "// Migrated to Google Test Framework\n"

    # Replace includes - add gtest
    if '#include <gtest/gtest.h>' not in content:
        # Find first #include and insert gtest before it
        content = re.sub(
            r'(#include\s+[<"])',
            r'#include <gtest/gtest.h>\n\1',
            content,
            count=1
        )

    # Remove old test framework macros
    content = re.sub(
        r'static\s+int\s+tests_passed\s*=\s*0;\s*\n'
        r'static\s+int\s+tests_failed\s*=\s*0;\s*\n',
        '',
        content
    )

    # Remove macro definitions
    content = re.sub(
        r'#define\s+TEST_START.*?\n'
        r'#define\s+TEST_PASS.*?\n.*?\n.*?\n'
        r'#define\s+TEST_FAIL.*?\n.*?\n.*?\n'
        r'#define\s+ASSERT\(.*?\n.*?\n.*?\n.*?\n',
        '',
        content,
        flags=re.MULTILINE | re.DOTALL
    )

    # Remove ASSERT_CONTAINS macro if present
    content = re.sub(
        r'#define\s+ASSERT_CONTAINS.*?\n.*?\n.*?\n.*?\n',
        '',
        content,
        flags=re.MULTILINE | re.DOTALL
    )

    # Remove ASSERT_NOT_EMPTY macro if present
    content = re.sub(
        r'#define\s+ASSERT_NOT_EMPTY.*?\n.*?\n.*?\n.*?\n',
        '',
        content,
        flags=re.MULTILINE | re.DOTALL
    )

    # Convert test functions to GTest TEST() macros
    # Pattern: void test_name() { TEST_START("test_name");
    def convert_test_function(match):
        test_name = match.group(1)
        test_body = match.group(2)

        # Remove TEST_START calls
        test_body = re.sub(r'\s*TEST_START\([^)]+\);\s*\n', '', test_body)

        # Remove TEST_PASS calls
        test_body = re.sub(r'\s*TEST_PASS\([^)]+\);\s*', '', test_body)

        # Convert ASSERT to EXPECT_TRUE or ASSERT_NE
        test_body = re.sub(
            r'ASSERT\(([^,]+),\s*"([^"]+)"\)',
            r'EXPECT_TRUE(\1) << "\2"',
            test_body
        )

        # Convert ASSERT_CONTAINS
        test_body = re.sub(
            r'ASSERT_CONTAINS\(([^,]+),\s*([^,]+),\s*"([^"]+)"\)',
            r'EXPECT_NE(\1.find(\2), std::string::npos) << "\3"',
            test_body
        )

        # Convert ASSERT_NOT_EMPTY
        test_body = re.sub(
            r'ASSERT_NOT_EMPTY\(([^,]+),\s*"([^"]+)"\)',
            r'EXPECT_FALSE(\1.empty()) << "\2"',
            test_body
        )

        # Convert test name to CamelCase for GTest
        parts = test_name.split('_')
        camel_name = ''.join(p.capitalize() for p in parts if p not in ['test'])

        return f'TEST(IntegrationTest, {camel_name}) {{\n{test_body}\n}}'

    content = re.sub(
        r'void\s+(test_\w+)\(\)\s*\{(.*?)\n\}',
        convert_test_function,
        content,
        flags=re.MULTILINE | re.DOTALL
    )

    # Replace main() function with GTest main
    content = re.sub(
        r'int\s+main\(\)\s*\{.*?\}',
        '''int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}''',
        content,
        flags=re.MULTILINE | re.DOTALL
    )

    return content

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: migrate_tests.py <test_file>")
        sys.exit(1)

    file_path = Path(sys.argv[1])
    if not file_path.exists():
        print(f"Error: File {file_path} not found")
        sys.exit(1)

    print(f"Migrating {file_path}...")
    migrated_content = migrate_test_file(file_path)

    # Write back to file
    with open(file_path, 'w') as f:
        f.write(migrated_content)

    print(f"Successfully migrated {file_path}")
