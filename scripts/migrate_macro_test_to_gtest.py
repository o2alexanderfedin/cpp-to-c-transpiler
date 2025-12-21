#!/usr/bin/env python3
"""
Script to migrate macro-based test files (TEST_START/TEST_PASS) to GTest format.
Handles the specific test pattern used in the hupyy-cpp-to-c project.
"""

import re
import sys
from pathlib import Path
from typing import List, Tuple


def extract_test_functions(content: str) -> List[Tuple[str, str, str, bool]]:
    """
    Extract test functions from content.
    Returns list of (function_name, full_function, test_name, uses_astcontext) tuples.
    """
    # Pattern 1: void test_FunctionName() { ... }
    # Pattern 2: void test_FunctionName(ASTContext &Ctx) { ... }
    pattern = r'void\s+(test_\w+)\s*\(([^)]*)\)\s*\{((?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)\}'
    matches = re.finditer(pattern, content, re.MULTILINE | re.DOTALL)

    tests = []
    for match in matches:
        func_name = match.group(1)
        params = match.group(2).strip()
        func_body = match.group(3)
        uses_astcontext = 'ASTContext' in params

        # Extract test name from TEST_START macro
        test_name_match = re.search(r'TEST_START\s*\(\s*"([^"]+)"\s*\)', func_body)
        test_name = test_name_match.group(1) if test_name_match else func_name.replace('test_', '')
        # Clean up test name - replace special chars with valid C++ identifiers
        test_name = test_name.replace('()', '').replace(' ', '_').replace('-', '_')

        tests.append((func_name, match.group(0), test_name, uses_astcontext))

    return tests


def extract_helper_functions(content: str) -> str:
    """Extract helper functions section (not test functions, not main)."""
    # Find the section between includes and first test function
    lines = content.split('\n')
    helper_lines = []
    in_helper_section = False
    past_includes = False

    for i, line in enumerate(lines):
        # Skip until past includes
        if not past_includes:
            if line.strip() and not line.strip().startswith('#include') and not line.strip().startswith('//') and not line.strip().startswith('/*'):
                past_includes = True

        if past_includes and not in_helper_section:
            # Look for helper section markers
            if 'Helper' in line or 'helper' in line or line.strip().startswith('std::unique_ptr') or line.strip().startswith('FunctionDecl') or line.strip().startswith('CallingConv'):
                in_helper_section = True

        if in_helper_section:
            # Stop at first test function
            if 'void test_' in line or 'int main(' in line:
                break
            # Skip macro definitions
            if not line.strip().startswith('#define'):
                helper_lines.append(line)

    return '\n'.join(helper_lines).strip()


def convert_test_body(body: str) -> str:
    """Convert test body from macro format to GTest format."""
    # Remove TEST_START
    body = re.sub(r'\s*TEST_START\s*\([^)]+\)\s*;?', '', body)

    # Remove TEST_PASS
    body = re.sub(r'\s*TEST_PASS\s*\([^)]+\)\s*;?', '', body)

    # Replace TEST_FAIL with FAIL() << message
    body = re.sub(
        r'TEST_FAIL\s*\(\s*"[^"]*"\s*,\s*([^)]+)\)\s*;?\s*return\s*;?',
        r'FAIL() << \1;',
        body
    )

    # Replace ASSERT macro with ASSERT_TRUE
    body = re.sub(
        r'ASSERT\s*\(\s*([^,]+?)\s*,\s*([^)]+)\)\s*;?',
        r'ASSERT_TRUE(\1) << \2;',
        body
    )

    # Replace ASSERT_CONTAINS with EXPECT_NE(haystack.find(needle), std::string::npos)
    body = re.sub(
        r'ASSERT_CONTAINS\s*\(\s*([^,]+?)\s*,\s*([^,]+?)\s*,\s*([^)]+)\)\s*;?',
        r'EXPECT_NE((\1).find(\2), std::string::npos) << \3;',
        body
    )

    # Replace ASSERT_NOT_CONTAINS
    body = re.sub(
        r'ASSERT_NOT_CONTAINS\s*\(\s*([^,]+?)\s*,\s*([^,]+?)\s*,\s*([^)]+)\)\s*;?',
        r'EXPECT_EQ((\1).find(\2), std::string::npos) << \3;',
        body
    )

    # Replace ASSERT_EQUALS
    body = re.sub(
        r'ASSERT_EQUALS\s*\(\s*([^,]+?)\s*,\s*([^,]+?)\s*,\s*([^)]+)\)\s*;?',
        r'ASSERT_EQ(\1, \2) << \3;',
        body
    )

    # Replace TEST_PLATFORM_LIMITED
    body = re.sub(r'\s*TEST_PLATFORM_LIMITED\s*\([^)]+\)\s*;?', '', body)

    # Clean up excess whitespace
    body = re.sub(r'\n\n\n+', '\n\n', body)

    return body.strip()


def extract_includes(content: str) -> List[str]:
    """Extract include statements from content."""
    includes = []
    for line in content.split('\n'):
        if line.strip().startswith('#include'):
            # Skip test framework includes
            if 'iostream' not in line:
                includes.append(line.strip())
    return includes


def extract_static_variables(content: str) -> List[str]:
    """Extract static variables like persistentASTs."""
    statics = []
    pattern = r'static\s+(?:std::)?(?:vector|int|bool|string)<[^>]+>\s+\w+(?:\s*=\s*[^;]+)?;'
    matches = re.finditer(pattern, content, re.MULTILINE)
    for match in matches:
        statics.append(match.group(0))
    return statics


def migrate_test_file(input_path: Path) -> bool:
    """Migrate a single test file to GTest format (in-place)."""

    with open(input_path, 'r') as f:
        content = f.read()

    # Extract components
    test_functions = extract_test_functions(content)
    if not test_functions:
        print(f"⚠ No test functions found in {input_path}")
        return False

    includes = extract_includes(content)
    helpers = extract_helper_functions(content)
    statics = extract_static_variables(content)

    # Extract comments at top
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
    for inc in includes:
        output_lines.append(inc)

    output_lines.append("")
    output_lines.append("using namespace clang;")
    output_lines.append("")

    # Add static variables if any
    if statics:
        for static in statics:
            output_lines.append(static)
        output_lines.append("")

    # Add helper functions
    if helpers:
        output_lines.append(helpers)
        output_lines.append("")

    # Determine test suite name
    test_suite = input_path.stem.replace('Test', '')

    # Check if we need a fixture
    needs_fixture = ('buildAST' in helpers or 'persistentASTs' in helpers) or 'persistentASTs' in content

    if needs_fixture:
        output_lines.append(f"// Test fixture")
        output_lines.append(f"class {test_suite}Test : public ::testing::Test {{")
        output_lines.append("protected:")

        # Extract and add setup/teardown if needed
        if 'persistentASTs' in content:
            output_lines.append("    static std::vector<std::unique_ptr<ASTUnit>> persistentASTs;")

        output_lines.append("};")
        output_lines.append("")

        if 'persistentASTs' in content:
            output_lines.append(f"std::vector<std::unique_ptr<ASTUnit>> {test_suite}Test::persistentASTs;")
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
        print("Usage: migrate_macro_test_to_gtest.py <test_file> [<test_file2> ...]")
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
