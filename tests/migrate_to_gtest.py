#!/usr/bin/env python3
"""
Script to migrate custom test framework tests to Google Test framework.

This script automates the conversion of test files from the custom test
framework (using TEST_START, TEST_PASS, ASSERT macros) to Google Test
(using TEST_F, EXPECT_*, ASSERT_* macros).
"""

import re
import sys
from pathlib import Path

def convert_test_to_gtest(source_file: Path, output_file: Path, test_class_name: str):
    """
    Convert a test file from custom framework to GTest.

    Args:
        source_file: Path to source test file
        output_file: Path to output GTest file
        test_class_name: Name of the test fixture class
    """

    with open(source_file, 'r') as f:
        content = f.read()

    # Extract file header comment
    header_match = re.search(r'/\*\*.*?\*/', content, re.DOTALL)
    header_comment = header_match.group(0) if header_match else ""

    # Update header comment to note migration
    if "Migrated to GTest" not in header_comment:
        header_comment = header_comment.replace(
            "@brief Tests for",
            "@brief Tests for"
        ).replace("*/", " (Migrated to GTest)\n */")

    # Extract includes (everything between headers and buildAST function)
    includes_match = re.search(
        r'(#include.*?)(?=std::unique_ptr|using namespace)',
        content,
        re.DOTALL
    )

    includes = includes_match.group(1) if includes_match else ""

    # Remove old custom macros from includes
    includes = re.sub(r'#define TEST_START.*?\n', '', includes)
    includes = re.sub(r'#define TEST_PASS.*?\n', '', includes)
    includes = re.sub(r'#define ASSERT\(.*?\n.*?\n.*?\n.*?\n.*?\n', '', includes, flags=re.DOTALL)

    # Add GTest include if not present
    if '#include <gtest/gtest.h>' not in includes:
        includes = '#include <gtest/gtest.h>\n' + includes

    # Add test base header
    if '#include "../VirtualTableTestBase.h"' not in includes:
        includes = includes.replace(
            '#include <gtest/gtest.h>',
            '#include <gtest/gtest.h>\n#include "../VirtualTableTestBase.h"'
        )

    # Extract helper functions (like findClass, buildAST)
    helpers = ""

    # Find all test functions
    test_pattern = r'void (test_\w+)\(\) \{(.*?)\n\}'
    tests = re.findall(test_pattern, content, re.DOTALL)

    # Build the new test file content
    output_lines = []
    output_lines.append(header_comment)
    output_lines.append("\n")
    output_lines.append(includes)
    output_lines.append("\n")
    output_lines.append("using namespace clang;\n")
    output_lines.append("\n")
    output_lines.append(f"// Test fixture for {test_class_name} tests\n")

    # Determine base class (VirtualTableTestBase or VirtualInheritanceTestBase)
    base_class = "VirtualInheritanceTestBase" if "Virtual" in test_class_name and ("Base" in test_class_name or "VTT" in test_class_name) else "VirtualTableTestBase"

    output_lines.append(f"class {test_class_name} : public {base_class} {{\n")
    output_lines.append("};\n")
    output_lines.append("\n")

    # Convert each test function
    for test_name, test_body in tests:
        # Convert test name from test_FooBar to FooBar
        gtest_name = test_name.replace('test_', '')
        gtest_name = ''.join(word.capitalize() for word in gtest_name.split('_'))

        output_lines.append(f"// {gtest_name} Test\n")
        output_lines.append(f"TEST_F({test_class_name}, {gtest_name}) {{\n")

        # Convert test body
        converted_body = convert_test_body(test_body)
        output_lines.append(converted_body)
        output_lines.append("}\n")
        output_lines.append("\n")

    # Write output
    with open(output_file, 'w') as f:
        f.write(''.join(output_lines))

    print(f"Migrated: {source_file.name} -> {output_file.name}")
    return len(tests)

def convert_test_body(body: str) -> str:
    """Convert test body from custom framework to GTest."""

    # Remove TEST_START and TEST_PASS macros
    body = re.sub(r'\s*TEST_START\([^)]+\);\s*', '', body)
    body = re.sub(r'\s*TEST_PASS\([^)]+\);\s*', '', body)

    # Convert ASSERT(cond, msg) to ASSERT/EXPECT macros
    # This is complex because we need to handle multiline conditions

    # Convert simple assertions
    body = re.sub(
        r'ASSERT\(([^,]+),\s*"([^"]+)"\)',
        r'ASSERT_TRUE(\1) << "\2"',
        body
    )

    # Convert != nullptr checks
    body = re.sub(
        r'ASSERT_TRUE\((\w+) != nullptr\)',
        r'ASSERT_NE(\1, nullptr)',
        body
    )

    # Convert == checks
    body = re.sub(
        r'ASSERT_TRUE\(([^)]+) == ([^)]+)\)',
        r'ASSERT_EQ(\1, \2)',
        body
    )

    # Convert != checks
    body = re.sub(
        r'ASSERT_TRUE\(([^)]+) != ([^)]+)\)',
        r'ASSERT_NE(\1, \2)',
        body
    )

    # Convert >= checks
    body = re.sub(
        r'ASSERT_TRUE\(([^)]+) >= ([^)]+)\)',
        r'ASSERT_GE(\1, \2)',
        body
    )

    # Convert > checks
    body = re.sub(
        r'ASSERT_TRUE\(([^)]+) > ([^)]+)\)',
        r'ASSERT_GT(\1, \2)',
        body
    )

    # Convert < checks
    body = re.sub(
        r'ASSERT_TRUE\(([^)]+) < ([^)]+)\)',
        r'ASSERT_LT(\1, \2)',
        body
    )

    # Convert ! checks (negation)
    body = re.sub(
        r'ASSERT_TRUE\(!([^)]+)\)',
        r'ASSERT_FALSE(\1)',
        body
    )

    # Handle .find() != std::string::npos pattern
    body = re.sub(
        r'ASSERT_NE\(([^(]+)\.find\(([^)]+)\), std::string::npos\)',
        r'EXPECT_NE(\1.find(\2), std::string::npos)',
        body
    )

    # Handle .find() == std::string::npos pattern
    body = re.sub(
        r'ASSERT_EQ\(([^(]+)\.find\(([^)]+)\), std::string::npos\)',
        r'EXPECT_EQ(\1.find(\2), std::string::npos)',
        body
    )

    # Convert remaining ASSERT_TRUE to EXPECT_TRUE where appropriate
    # (keep critical assertions as ASSERT, convert others to EXPECT)
    body = re.sub(
        r'ASSERT_TRUE\(([^)]+)\) << "Expected',
        r'EXPECT_TRUE(\1) << "Expected',
        body
    )

    return body

def main():
    """Main migration function."""

    # Define test files to migrate with their class names
    test_files = {
        "VirtualMethodAnalyzerTest.cpp": "VirtualMethodAnalyzerTest",
        "VirtualCallTranslatorTest.cpp": "VirtualCallTranslatorTest",
        "VirtualBaseDetectionTest.cpp": "VirtualBaseDetectionTest",
        "VirtualBaseOffsetTableTest.cpp": "VirtualBaseOffsetTableTest",
        "VptrInjectorTest.cpp": "VptrInjectorTest",
        "VTTGeneratorTest.cpp": "VTTGeneratorTest",
        "VtableInitializerTest.cpp": "VtableInitializerTest",
        "OverrideResolverTest.cpp": "OverrideResolverTest",
        "HierarchyTraversalTest.cpp": "HierarchyTraversalTest",
        "DynamicCastTranslatorTest.cpp": "DynamicCastTranslatorTest",
        "DynamicCastCrossCastTest.cpp": "DynamicCastCrossCastTest",
        "CrossCastTraversalTest.cpp": "CrossCastTraversalTest",
        "TypeidTranslatorTest.cpp": "TypeidTranslatorTest",
        "TypeInfoGeneratorTest.cpp": "TypeInfoGeneratorTest",
        "PureVirtualHandlerTest.cpp": "PureVirtualHandlerTest",
    }

    base_dir = Path(__file__).parent
    source_dir = base_dir
    output_dir = base_dir / "virtual_inheritance_tests"

    total_tests = 0
    for filename, classname in test_files.items():
        source = source_dir / filename
        output = output_dir / filename

        if source.exists():
            try:
                num_tests = convert_test_to_gtest(source, output, classname)
                total_tests += num_tests
                print(f"  Converted {num_tests} tests")
            except Exception as e:
                print(f"ERROR migrating {filename}: {e}", file=sys.stderr)
        else:
            print(f"WARNING: Source file not found: {source}", file=sys.stderr)

    print(f"\nTotal tests migrated: {total_tests}")
    print(f"Output directory: {output_dir}")

if __name__ == "__main__":
    main()
