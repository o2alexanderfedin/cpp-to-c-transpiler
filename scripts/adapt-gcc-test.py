#!/usr/bin/env python3
"""
GCC C++23 Test Adapter
Converts GCC-specific test format to standalone C++ files for Phase 33.2

This script:
1. Strips GCC-specific directives (dg-do, dg-options, dg-error, dg-warning, etc.)
2. Wraps code in standalone C++ structure with main() if needed
3. Preserves original test intent and includes proper headers
4. Supports batch processing with consistent naming

Usage:
    Single file:
        python3 scripts/adapt-gcc-test.py \\
            --input external-projects/gcc-tests/if-consteval-P1938/consteval-if1.C \\
            --output gcc-adapted/if-consteval-P1938/test01.cpp \\
            --category if-consteval

    Directory:
        python3 scripts/adapt-gcc-test.py \\
            --input-dir external-projects/gcc-tests/if-consteval-P1938 \\
            --output-dir gcc-adapted/if-consteval-P1938 \\
            --category if-consteval

Author: Phase 33.2 - GCC C++23 Test Validation
License: Same as HUpyy project
"""

import argparse
import os
import re
import sys
from pathlib import Path
from typing import Tuple, List, Optional


class GCCTestAdapter:
    """Adapter for converting GCC test format to standalone C++ files."""

    # Regex patterns for GCC-specific directives
    DG_PATTERNS = [
        r'//\s*\{\s*dg-do\s+.*?\s*\}',  # dg-do compile/run
        r'//\s*\{\s*dg-options\s+.*?\s*\}',  # dg-options
        r'//\s*\{\s*dg-error\s+.*?\s*\}',  # dg-error
        r'//\s*\{\s*dg-warning\s+.*?\s*\}',  # dg-warning
        r'//\s*\{\s*dg-message\s+.*?\s*\}',  # dg-message
        r'//\s*\{\s*dg-note\s+.*?\s*\}',  # dg-note
        r'//\s*\{\s*dg-excess\s+.*?\s*\}',  # dg-excess
        r'//\s*\{\s*target\s+.*?\s*\}',  # target conditionals
        r'//\s*\{\s*dg-bogus\s+.*?\s*\}',  # dg-bogus
    ]

    def __init__(self, verbose: bool = False):
        """Initialize the adapter."""
        self.verbose = verbose
        self.dg_regex = re.compile('|'.join(self.DG_PATTERNS))

    def strip_gcc_directives(self, content: str) -> str:
        """
        Remove all GCC-specific directives from code.

        Args:
            content: Original file content

        Returns:
            Content with GCC directives removed
        """
        lines = content.split('\n')
        result = []

        for line in lines:
            # Check if line is entirely a dg directive comment
            # Pattern: // { dg-* ... }
            if re.match(r'^\s*//\s*\{\s*dg-', line):
                # Skip lines that are ONLY dg directives
                continue

            # For other lines, remove inline dg directives while preserving code
            # The dg directive is always after the code, in a comment block like:
            # code { dg-warning "..." { target ... } }
            # We need to preserve code but remove the directive
            # Find where the dg directive starts and remove from there

            # Look for the pattern: { dg-* ... } possibly followed by more }
            # We want to remove from the opening { of the dg directive onwards
            match = re.search(r'\s*\{\s*dg-', line)
            if match:
                # Found a dg directive, remove from this point onwards
                # But we need to handle nested braces properly
                # For safety, just remove everything after the last code before the dg directive
                code_part = line[:match.start()]
                stripped = code_part.rstrip()
            else:
                stripped = line

            # Also remove trailing comment markers that are just "//"
            stripped = re.sub(r'\s+//\s*$', '', stripped)

            result.append(stripped)

        # Remove trailing empty lines
        while result and result[-1] == '':
            result.pop()

        return '\n'.join(result)

    def needs_main_wrapper(self, content: str) -> bool:
        """
        Determine if code needs a main() wrapper.

        Args:
            content: Cleaned code content

        Returns:
            True if main() wrapper is needed
        """
        # Check if code already has main function
        return not re.search(r'\bmain\s*\(', content)

    def needs_iostream(self, content: str) -> bool:
        """
        Determine if code needs iostream header.

        Args:
            content: Cleaned code content

        Returns:
            True if iostream is needed
        """
        # Check for stdout/stderr usage
        return re.search(r'std::(cout|cerr|clog)|std::endl|std::flush', content)

    def get_required_headers(self, content: str) -> List[str]:
        """
        Determine which standard headers are needed.

        Args:
            content: Cleaned code content

        Returns:
            List of required headers
        """
        headers = []

        # Check for cassert usage
        if re.search(r'\bassert\s*\(', content) or 'static_assert' in content:
            headers.append('<cassert>')

        # Check for iostream usage
        if self.needs_iostream(content):
            headers.append('<iostream>')

        # Check for stdexcept usage
        if re.search(r'std::exception|std::runtime_error|throw\s+', content):
            headers.append('<stdexcept>')

        # Check for vector/array usage
        if re.search(r'std::vector|std::array|std::deque', content):
            headers.append('<vector>')

        # Check for memory usage
        if re.search(r'std::unique_ptr|std::shared_ptr|std::make_unique', content):
            headers.append('<memory>')

        # Check for type_traits usage
        if re.search(r'std::is_same|std::enable_if|std::decay', content):
            headers.append('<type_traits>')

        # Check for limits usage
        if re.search(r'std::numeric_limits', content):
            headers.append('<limits>')

        # Check for cstdlib usage (for abort, etc.)
        if re.search(r'abort\s*\(\)|exit\s*\(', content):
            headers.append('<cstdlib>')

        # Remove duplicates and sort
        return sorted(list(set(headers)))

    def wrap_in_main(self, content: str) -> str:
        """
        Wrap code in main() function if needed.

        Args:
            content: Cleaned code content

        Returns:
            Code wrapped in main() if necessary
        """
        if not self.needs_main_wrapper(content):
            return content

        # Strategy: Track brace depth to distinguish between
        # - Global scope (brace_depth = 0)
        # - Inside function/class/namespace (brace_depth > 0)
        lines = content.split('\n')
        global_lines = []
        code_lines = []
        brace_depth = 0
        in_function = False

        for line in lines:
            stripped = line.strip()

            # Skip empty lines initially
            if stripped == '':
                if brace_depth == 0:
                    global_lines.append(line)
                else:
                    code_lines.append(line)
                continue

            # Count braces to track scope
            open_braces = stripped.count('{') - stripped.count('{{')
            close_braces = stripped.count('}') - stripped.count('}}')
            net_braces = open_braces - close_braces

            # Check if this is a declaration that should stay global
            is_global_decl = any(
                stripped.startswith(prefix)
                for prefix in [
                    'template',
                    'class ',
                    'struct ',
                    'namespace ',
                    'using ',
                    'extern ',
                    'typedef ',
                    '#include',
                    '#define',
                    '#pragma',
                ]
            ) or (
                # Variable or function declaration at global scope
                brace_depth == 0
                and (
                    re.match(r'^(const|constexpr|static|inline|extern)\s+', stripped)
                    or re.match(r'^static_assert\s*\(', stripped)
                )
            )

            if is_global_decl:
                global_lines.append(line)
                brace_depth += net_braces
                if net_braces > 0:
                    in_function = True
                if brace_depth == 0 and net_braces < 0:
                    in_function = False
                continue

            # Check for function definition at global scope
            if (
                brace_depth == 0
                and re.match(r'^(void|int|bool|auto|constexpr|static)\s+\w+\s*\([^)]*\)', stripped)
            ):
                global_lines.append(line)
                brace_depth += net_braces
                in_function = True
                continue

            # Anything else at global scope
            if brace_depth == 0:
                # Could be a statement that needs wrapping, or another declaration
                if '{' not in stripped or net_braces <= 0:
                    code_lines.append(line)
                    brace_depth += net_braces
                else:
                    global_lines.append(line)
                    brace_depth += net_braces
            else:
                # Inside a function/class - keep with global section
                global_lines.append(line)
                brace_depth += net_braces

        # If we have code to wrap, create main()
        if code_lines or (not global_lines and content.strip()):
            global_section = '\n'.join(global_lines).rstrip()
            code_section = '\n'.join(code_lines).rstrip()

            if global_section:
                return f"""{global_section}

int main()
{{
  {code_section}
  return 0;
}}"""
            else:
                return f"""int main()
{{
  {code_section}
  return 0;
}}"""

        return content

    def generate_header_comment(
        self,
        original_file: str,
        category: str,
        test_number: int
    ) -> str:
        """
        Generate header comment for adapted test.

        Args:
            original_file: Original GCC test filename
            category: Test category name
            test_number: Test number in sequence

        Returns:
            Header comment string
        """
        return f"""// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: {original_file}
// Category: {category}
// Test ID: {test_number:02d}
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

"""

    def adapt(
        self,
        content: str,
        original_file: str = '',
        category: str = 'misc',
        test_number: int = 1
    ) -> str:
        """
        Adapt GCC test to standalone C++ format.

        Args:
            content: Original GCC test content
            original_file: Original filename for documentation
            category: Test category
            test_number: Test number in sequence

        Returns:
            Adapted C++ code
        """
        # Step 1: Add header comment
        header = self.generate_header_comment(original_file, category, test_number)

        # Step 2: Strip GCC directives
        cleaned = self.strip_gcc_directives(content)

        # Step 3: Determine required headers
        required_headers = self.get_required_headers(cleaned)

        # Step 4: Wrap in main if needed
        wrapped = self.wrap_in_main(cleaned)

        # Step 5: Build final output
        includes = '\n'.join(f'#include {h}' for h in required_headers)
        if includes:
            includes += '\n'

        return f"{header}{includes}{wrapped}\n"

    def process_file(
        self,
        input_file: str,
        output_file: str,
        category: str = 'misc',
        test_number: int = 1
    ) -> bool:
        """
        Process single GCC test file.

        Args:
            input_file: Path to input GCC test file
            output_file: Path to output C++ file
            category: Test category
            test_number: Test number in sequence

        Returns:
            True if successful
        """
        try:
            # Try to read file with UTF-8, fall back to latin-1
            content = None
            for encoding in ['utf-8', 'latin-1', 'iso-8859-1', 'cp1252']:
                try:
                    with open(input_file, 'r', encoding=encoding) as f:
                        content = f.read()
                    break
                except (UnicodeDecodeError, LookupError):
                    continue

            if content is None:
                print(
                    f"✗ Error processing {input_file}: Could not decode file",
                    file=sys.stderr
                )
                return False

            # Adapt content
            adapted = self.adapt(
                content,
                original_file=Path(input_file).name,
                category=category,
                test_number=test_number
            )

            # Create output directory if needed
            output_path = Path(output_file)
            output_path.parent.mkdir(parents=True, exist_ok=True)

            # Write output file
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write(adapted)

            if self.verbose:
                print(f"✓ Adapted {input_file} -> {output_file}")

            return True

        except Exception as e:
            print(f"✗ Error processing {input_file}: {e}", file=sys.stderr)
            return False

    def process_directory(
        self,
        input_dir: str,
        output_dir: str,
        category: str = 'misc',
        pattern: str = '*.C'
    ) -> Tuple[int, int]:
        """
        Process all GCC test files in directory.

        Args:
            input_dir: Path to input directory
            output_dir: Path to output directory
            category: Test category
            pattern: File pattern to match (default: *.C)

        Returns:
            Tuple of (processed, failed)
        """
        input_path = Path(input_dir)
        output_path = Path(output_dir)

        if not input_path.is_dir():
            print(f"✗ Input directory not found: {input_dir}", file=sys.stderr)
            return 0, 1

        # Find all test files
        test_files = sorted(input_path.glob(pattern))

        if not test_files:
            print(f"✗ No test files matching {pattern} in {input_dir}", file=sys.stderr)
            return 0, 1

        processed = 0
        failed = 0

        for idx, test_file in enumerate(test_files, 1):
            output_file = output_path / f"test{idx:02d}.cpp"
            if self.process_file(str(test_file), str(output_file), category, idx):
                processed += 1
            else:
                failed += 1

        return processed, failed

    def generate_cmake_for_category(
        self,
        output_dir: str,
        category: str,
        test_count: int
    ) -> bool:
        """
        Generate CMakeLists.txt for test category.

        Args:
            output_dir: Output directory path
            category: Test category name
            test_count: Number of tests in category

        Returns:
            True if successful
        """
        try:
            cmake_content = f'''cmake_minimum_required(VERSION 3.12)

project({category}-cpp23-tests)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Test sources
set(TEST_SOURCES
'''

            for i in range(1, test_count + 1):
                cmake_content += f'    test{i:02d}.cpp\n'

            cmake_content += ''')

# For each test file, create an executable
foreach(test_file ${TEST_SOURCES})
    get_filename_component(test_name ${test_file} NAME_WE)
    add_executable(${test_name} ${test_file})
    set_target_properties(${test_name} PROPERTIES
        CXX_STANDARD 23
        CXX_STANDARD_REQUIRED ON
    )
    add_test(NAME ${test_name} COMMAND ${test_name})
endforeach()

enable_testing()
'''

            cmake_path = Path(output_dir) / 'CMakeLists.txt'
            cmake_path.parent.mkdir(parents=True, exist_ok=True)

            with open(cmake_path, 'w', encoding='utf-8') as f:
                f.write(cmake_content)

            if self.verbose:
                print(f"✓ Generated CMakeLists.txt in {output_dir}")

            return True

        except Exception as e:
            print(f"✗ Error generating CMakeLists.txt: {e}", file=sys.stderr)
            return False


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Adapt GCC C++23 tests to standalone C++ files',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  # Single file adaptation
  %(prog)s --input test.C --output test.cpp --category if-consteval

  # Batch directory processing
  %(prog)s --input-dir gcc-tests/if-consteval-P1938 \\
           --output-dir adapted/if-consteval-P1938 \\
           --category if-consteval

  # With CMakeLists.txt generation
  %(prog)s --input-dir gcc-tests/miscellaneous \\
           --output-dir adapted/misc \\
           --category miscellaneous \\
           --generate-cmake
        '''
    )

    parser.add_argument(
        '--input',
        type=str,
        help='Input GCC test file'
    )
    parser.add_argument(
        '--output',
        type=str,
        help='Output C++ file'
    )
    parser.add_argument(
        '--input-dir',
        type=str,
        help='Input directory with GCC test files'
    )
    parser.add_argument(
        '--output-dir',
        type=str,
        help='Output directory for C++ files'
    )
    parser.add_argument(
        '--category',
        type=str,
        default='misc',
        help='Test category name (default: misc)'
    )
    parser.add_argument(
        '--pattern',
        type=str,
        default='*.C',
        help='File pattern for directory processing (default: *.C)'
    )
    parser.add_argument(
        '--generate-cmake',
        action='store_true',
        help='Generate CMakeLists.txt for category'
    )
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='Verbose output'
    )

    args = parser.parse_args()

    # Validate arguments
    if not args.input and not args.input_dir:
        parser.error('Either --input or --input-dir is required')

    if args.input and not args.output:
        parser.error('--output is required when using --input')

    if args.input_dir and not args.output_dir:
        parser.error('--output-dir is required when using --input-dir')

    adapter = GCCTestAdapter(verbose=args.verbose)

    # Single file processing
    if args.input:
        success = adapter.process_file(
            args.input,
            args.output,
            args.category,
            1
        )
        return 0 if success else 1

    # Directory processing
    if args.input_dir:
        processed, failed = adapter.process_directory(
            args.input_dir,
            args.output_dir,
            args.category,
            args.pattern
        )

        print(f"\nProcessing complete:")
        print(f"  Processed: {processed}")
        print(f"  Failed: {failed}")

        if args.generate_cmake and processed > 0:
            adapter.generate_cmake_for_category(
                args.output_dir,
                args.category,
                processed
            )

        return 0 if failed == 0 else 1

    return 0


if __name__ == '__main__':
    sys.exit(main())
