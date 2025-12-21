#!/usr/bin/env python3
"""
Script to migrate complex test files with deep nesting.
Uses a manual brace-counting parser instead of regex.
"""

import re
import sys
from pathlib import Path
from typing import List, Tuple


def extract_test_functions_robust(content: str) -> List[Tuple[str, str, str, bool]]:
    """
    Extract test functions using manual parsing for deep nesting.
    Returns list of (function_name, full_function, test_name, uses_astcontext) tuples.
    """
    lines = content.split('\n')
    tests = []
    i = 0

    while i < len(lines):
        line = lines[i]

        # Look for test function declaration (void or bool)
        match = re.match(r'\s*(?:void|bool)\s+(test_\w+)\s*\(([^)]*)\)\s*\{?\s*$', line)
        if match:
            func_name = match.group(1)
            params = match.group(2).strip()
            uses_astcontext = 'ASTContext' in params

            # Find the opening brace (might be on next line)
            func_start = i
            if '{' not in line:
                i += 1
                while i < len(lines) and '{' not in lines[i]:
                    i += 1

            # Count braces to find the closing brace
            brace_count = 0
            func_lines = []
            started = False

            for j in range(func_start, len(lines)):
                func_lines.append(lines[j])
                for char in lines[j]:
                    if char == '{':
                        brace_count += 1
                        started = True
                    elif char == '}':
                        brace_count -= 1
                        if started and brace_count == 0:
                            # Found the end of function
                            full_func = '\n'.join(func_lines)

                            # Extract test name from TEST_START
                            test_name_match = re.search(r'TEST_START\s*\(\s*"([^"]+)"\s*\)', full_func)
                            test_name = test_name_match.group(1) if test_name_match else func_name.replace('test_', '')
                            test_name = test_name.replace('()', '').replace(' ', '_').replace('-', '_')

                            tests.append((func_name, full_func, test_name, uses_astcontext))
                            i = j
                            break
                if started and brace_count == 0:
                    break

        i += 1

    return tests


def extract_helper_section(content: str) -> str:
    """Extract helper functions and utilities."""
    lines = content.split('\n')
    helper_lines = []
    capturing = False
    test_started = False

    for line in lines:
        # Stop at first test function
        if re.match(r'\s*(?:void|bool)\s+test_\w+\s*\(', line):
            test_started = True
            break

        # Skip includes, comments, macros
        if (line.strip().startswith('#include') or
            line.strip().startswith('//') or
            line.strip().startswith('/*') or
            line.strip().startswith('*') or
            line.strip().startswith('#define')):
            continue

        # Skip using namespace
        if 'using namespace' in line:
            continue

        # Capture everything else before tests
        if line.strip() and not test_started:
            capturing = True

        if capturing and not test_started:
            helper_lines.append(line)

    return '\n'.join(helper_lines).strip()


def convert_test_body(body: str) -> str:
    """Convert test body from macro format to GTest format."""
    # Remove TEST_START
    body = re.sub(r'\s*TEST_START\s*\([^)]+\)\s*;?', '', body)

    # Remove TEST_PASS
    body = re.sub(r'\s*TEST_PASS\s*\([^)]+\)\s*;?', '', body)

    # Replace TEST_FAIL with FAIL()
    body = re.sub(
        r'TEST_FAIL\s*\(\s*"[^"]*"\s*,\s*([^)]+)\)\s*;?',
        r'FAIL() << \1;',
        body
    )

    # Remove return true/false at end
    body = re.sub(r'\s*return\s+(?:true|false)\s*;\s*$', '', body, flags=re.MULTILINE)

    # Replace ASSERT macro with ASSERT_TRUE
    body = re.sub(
        r'ASSERT\s*\(\s*([^,]+?)\s*,\s*([^)]+)\)\s*;?',
        r'ASSERT_TRUE(\1) << \2;',
        body
    )

    # Replace ASSERT_CONTAINS
    body = re.sub(
        r'ASSERT_CONTAINS\s*\(\s*([^,]+?)\s*,\s*([^,]+?)\s*,\s*([^)]+)\)\s*;?',
        r'EXPECT_NE((\1).find(\2), std::string::npos) << \3;',
        body
    )

    # Clean up excess whitespace
    body = re.sub(r'\n\n\n+', '\n\n', body)

    return body.strip()


def migrate_test_file(input_path: Path) -> bool:
    """Migrate a single test file to GTest format (in-place)."""

    with open(input_path, 'r') as f:
        content = f.read()

    # Extract components
    test_functions = extract_test_functions_robust(content)
    if not test_functions:
        print(f"⚠ No test functions found in {input_path}")
        return False

    helpers = extract_helper_section(content)

    # Extract header comments
    header_comments = []
    for line in content.split('\n'):
        if line.strip().startswith('//') or line.strip().startswith('/*') or line.strip().startswith('*'):
            header_comments.append(line)
        elif line.strip() and not line.strip().startswith('#'):
            break

    # Build new file
    output_lines = []

    # Add header comments
    if header_comments:
        output_lines.extend(header_comments)
        output_lines.append("")

    # Add GTest include
    output_lines.append("#include <gtest/gtest.h>")

    # Add other includes
    for line in content.split('\n'):
        if line.strip().startswith('#include') and 'iostream' not in line:
            output_lines.append(line.strip())

    output_lines.append("")
    output_lines.append("using namespace clang;")
    output_lines.append("")

    # Add helpers
    if helpers:
        output_lines.append(helpers)
        output_lines.append("")

    # Determine test suite name
    test_suite = input_path.stem.replace('Test', '')

    # Check if we need a fixture
    needs_fixture = 'buildAST' in helpers or 'persistentASTs' in content

    if needs_fixture:
        output_lines.append(f"// Test fixture")
        output_lines.append(f"class {test_suite}Test : public ::testing::Test {{")
        output_lines.append("protected:")
        output_lines.append("};")
        output_lines.append("")

    # Convert test functions
    for func_name, full_func, test_name, uses_astcontext in test_functions:
        # Extract function body
        match = re.search(r'\{(.*)\}', full_func, re.DOTALL)
        if not match:
            continue

        body = match.group(1)
        converted_body = convert_test_body(body)

        # Generate TEST or TEST_F
        if needs_fixture:
            output_lines.append(f"TEST_F({test_suite}Test, {test_name}) {{")
        else:
            output_lines.append(f"TEST({test_suite}, {test_name}) {{")

        # If test uses ASTContext, we need to create it
        if uses_astcontext:
            output_lines.append("    // Build AST for test")
            output_lines.append("    const char *code = R\"(int main() { return 0; })\";")
            output_lines.append("    std::unique_ptr<ASTUnit> AST = buildAST(code);")
            output_lines.append("    ASTContext &Ctx = AST->getASTContext();")
            output_lines.append("")

        # Add converted body with proper indentation
        for line in converted_body.split('\n'):
            if line.strip():
                output_lines.append(f"    {line}")
            else:
                output_lines.append("")

        output_lines.append("}")
        output_lines.append("")

    # Write back to file
    with open(input_path, 'w') as f:
        f.write('\n'.join(output_lines))

    print(f"✓ Migrated {input_path.name} ({len(test_functions)} tests)")
    return True


def main():
    if len(sys.argv) < 2:
        print("Usage: migrate_complex_tests.py <test_file> [<test_file2> ...]")
        sys.exit(1)

    success_count = 0
    fail_count = 0

    for arg in sys.argv[1:]:
        input_path = Path(arg)

        if not input_path.exists():
            print(f"✗ Error: File {input_path} does not exist")
            fail_count += 1
            continue

        if migrate_test_file(input_path):
            success_count += 1
        else:
            fail_count += 1

    print(f"\n=== Migration Summary ===")
    print(f"Success: {success_count}")
    print(f"Failed: {fail_count}")

    sys.exit(0 if fail_count == 0 else 1)


if __name__ == "__main__":
    main()
