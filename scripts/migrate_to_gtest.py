#!/usr/bin/env python3
"""
Script to migrate custom test files to GTest format.
Handles common patterns in the test suite.
"""

import re
import sys
from pathlib import Path


def migrate_test_file(input_path: Path, output_path: Path):
    """Migrate a single test file to GTest format."""

    with open(input_path, 'r') as f:
        content = f.read()

    # Extract test functions
    # Pattern 1: void test_Name() { ... }
    # Pattern 2: bool test_Name() { ... }
    test_functions = re.findall(
        r'((?:void|bool)\s+test_\w+\s*\([^)]*\)\s*{(?:[^{}]|{[^{}]*})*})',
        content,
        re.MULTILINE | re.DOTALL
    )

    if not test_functions:
        print(f"Warning: No test functions found in {input_path}")
        return False

    # Determine if tests use ASTContext parameter
    uses_astcontext = 'ASTContext &Ctx' in content or 'ASTContext& Ctx' in content

    # Create GTest output
    output_lines = []

    # Add header
    output_lines.append(f"// {output_path.name}")
    output_lines.append(f"// Migrated from {input_path.name} to Google Test framework")
    output_lines.append("")
    output_lines.append("#include <gtest/gtest.h>")

    # Extract includes from original file
    includes = re.findall(r'#include\s+[<"]([^>"]+)[>"]', content)
    seen_includes = set()
    for inc in includes:
        if inc not in seen_includes and 'iostream' not in inc:
            if inc.startswith('clang/') or inc.startswith('llvm/'):
                output_lines.append(f'#include "{inc}"')
            elif not inc.endswith('.h'):
                output_lines.append(f'#include "../include/{inc}.h"')
            else:
                output_lines.append(f'#include "../include/{inc}"')
            seen_includes.add(inc)

    output_lines.append("")
    output_lines.append("using namespace clang;")
    output_lines.append("")

    # Check if we need a fixture
    has_buildast_helper = 'buildAST(' in content or 'buildASTFromCode(' in content
    has_buildastwithargs = 'buildASTFromCodeWithArgs' in content

    if has_buildast_helper or uses_astcontext:
        output_lines.append("// Test fixture")
        test_class_name = output_path.stem.replace('Test_GTest', 'Test').replace('_GTest', 'Test')
        output_lines.append(f"class {test_class_name}Fixture : public ::testing::Test {{")
        output_lines.append("protected:")
        output_lines.append("    std::unique_ptr<ASTUnit> buildAST(const char *code) {")

        if has_buildastwithargs:
            output_lines.append("        std::vector<std::string> args = {\"-std=c++17\", \"-xc++\"};")
            output_lines.append("        return tooling::buildASTFromCodeWithArgs(code, args, \"test.cpp\");")
        else:
            output_lines.append("        return tooling::buildASTFromCode(code);")

        output_lines.append("    }")
        output_lines.append("};")
        output_lines.append("")

        fixture_name = f"{test_class_name}Fixture"
    else:
        fixture_name = None

    # Convert each test function
    for test_func in test_functions:
        # Extract test name
        match = re.search(r'test_(\w+)', test_func)
        if not match:
            continue

        test_name = match.group(1)

        # Convert function body
        # Remove function signature
        body = re.sub(r'^(?:void|bool)\s+test_\w+\s*\([^)]*\)\s*{', '', test_func)
        body = body.rstrip('}').strip()

        # Replace TEST_START, TEST_PASS, TEST_FAIL macros
        body = re.sub(r'TEST_START\([^)]+\);?', '', body)
        body = re.sub(r'TEST_PASS\([^)]+\);?', '', body)
        body = re.sub(r'TEST_FAIL\([^,]+,\s*([^)]+)\);?\s*return[^;]*;', r'FAIL() << \1; return;', body)

        # Replace ASSERT macro with ASSERT_TRUE
        body = re.sub(
            r'ASSERT\(([^,]+),\s*([^)]+)\);?',
            r'ASSERT_TRUE(\1) << \2;',
            body
        )

        # Replace assert with ASSERT_TRUE
        body = re.sub(r'assert\(([^&]+)&&\s*"([^"]+)"\);?', r'ASSERT_TRUE(\1) << "\2";', body)
        body = re.sub(r'assert\(([^)]+)\);?', r'ASSERT_TRUE(\1);', body)

        # Replace std::cout with proper handling
        body = re.sub(r'std::cout\s*<<[^;]+;\s*', '', body)
        body = re.sub(r'outs\(\)\s*<<[^;]+;\s*', '', body)

        # Remove return true/false at end
        body = re.sub(r'\s*return\s+(?:true|false);?\s*$', '', body)

        # Clean up ASTContext parameter references if present
        if uses_astcontext:
            body = re.sub(r'ASTContext\s+&Ctx\s*=\s*AST->getASTContext\(\);?', '', body)

        # Generate TEST or TEST_F
        if fixture_name:
            output_lines.append(f"TEST_F({fixture_name}, {test_name}) {{")
        else:
            suite_name = output_path.stem.replace('Test_GTest', '').replace('_GTest', '')
            output_lines.append(f"TEST({suite_name}, {test_name}) {{")

        # Add indented body
        for line in body.split('\n'):
            if line.strip():
                output_lines.append(f"    {line}")
            else:
                output_lines.append("")

        output_lines.append("}")
        output_lines.append("")

    # Write output file
    with open(output_path, 'w') as f:
        f.write('\n'.join(output_lines))

    print(f"✓ Migrated {input_path.name} -> {output_path.name} ({len(test_functions)} tests)")
    return True


def main():
    if len(sys.argv) < 3:
        print("Usage: migrate_to_gtest.py <input_file> <output_file>")
        sys.exit(1)

    input_path = Path(sys.argv[1])
    output_path = Path(sys.argv[2])

    if not input_path.exists():
        print(f"Error: Input file {input_path} does not exist")
        sys.exit(1)

    success = migrate_test_file(input_path, output_path)
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
