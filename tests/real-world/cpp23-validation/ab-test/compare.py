#!/usr/bin/env python3
"""
A/B Output Comparison Tool for Phase 33.3
Compares C++ transpiler outputs (C vs CPP) with intelligent normalization.
"""

import sys
import argparse
import os
import re
from difflib import unified_diff, SequenceMatcher
from pathlib import Path
from typing import List, Tuple, Optional
import io


class OutputNormalizer:
    """Normalizes outputs for comparison while preserving semantic differences."""

    def __init__(self, ignore_comments: bool = True, numeric_tolerance: float = 1e-10):
        self.ignore_comments = ignore_comments
        self.numeric_tolerance = numeric_tolerance

    def normalize_whitespace(self, text: str) -> str:
        """
        Normalize whitespace while preserving code structure.
        - Strip trailing whitespace from lines
        - Normalize line endings
        - Collapse multiple blank lines into single blank line
        """
        lines = text.split('\n')
        lines = [line.rstrip() for line in lines]

        # Remove multiple consecutive blank lines
        normalized = []
        prev_blank = False
        for line in lines:
            is_blank = not line.strip()
            if is_blank and prev_blank:
                continue
            normalized.append(line)
            prev_blank = is_blank

        return '\n'.join(normalized)

    def remove_comments(self, text: str) -> str:
        """Remove C/C++ style comments."""
        if not self.ignore_comments:
            return text

        # Remove single-line comments
        text = re.sub(r'//.*?$', '', text, flags=re.MULTILINE)

        # Remove multi-line comments
        text = re.sub(r'/\*.*?\*/', '', text, flags=re.DOTALL)

        return text

    def normalize_numbers(self, text: str) -> str:
        """Normalize floating point numbers within tolerance."""
        def normalize_float(match):
            try:
                num = float(match.group(0))
                # Round to significant digits for comparison
                return f"{num:.10g}"
            except (ValueError, AttributeError):
                return match.group(0)

        # Match floating point numbers (including scientific notation)
        pattern = r'[-+]?\d*\.?\d+(?:[eE][-+]?\d+)?'
        text = re.sub(pattern, normalize_float, text)
        return text

    def normalize_identifiers(self, text: str) -> str:
        """
        Normalize compiler-generated identifiers while preserving user code.
        Keep this minimal to avoid over-normalization.
        """
        return text

    def normalize(self, text: str) -> str:
        """Apply all normalization steps."""
        text = self.normalize_whitespace(text)
        text = self.remove_comments(text)
        text = self.normalize_numbers(text)
        text = self.normalize_identifiers(text)
        return text


class OutputComparator:
    """Compares two outputs with detailed reporting."""

    def __init__(self, verbose: bool = False, ignore_comments: bool = True):
        self.verbose = verbose
        self.normalizer = OutputNormalizer(ignore_comments=ignore_comments)
        self.color_enabled = self._check_color_support()

    def _check_color_support(self) -> bool:
        """Check if terminal supports colored output."""
        if not sys.stdout.isatty():
            return False

        term = os.environ.get('TERM', '').lower()
        if 'color' in term or 'xterm' in term or term == 'screen':
            return True

        return False

    def _colorize(self, text: str, color: str) -> str:
        """Apply color to text if color is enabled."""
        if not self.color_enabled:
            return text

        colors = {
            'red': '\033[91m',
            'green': '\033[92m',
            'yellow': '\033[93m',
            'blue': '\033[94m',
            'reset': '\033[0m',
        }
        return f"{colors.get(color, '')}{text}{colors['reset']}"

    def read_file(self, filepath: str) -> str:
        """Read file with error handling."""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                return f.read()
        except FileNotFoundError:
            print(self._colorize(f"Error: File not found: {filepath}", 'red'), file=sys.stderr)
            sys.exit(2)
        except Exception as e:
            print(self._colorize(f"Error reading {filepath}: {e}", 'red'), file=sys.stderr)
            sys.exit(2)

    def compare_files(self, file1: str, file2: str) -> Tuple[bool, dict]:
        """
        Compare two files and return (is_match, details).

        Returns:
            Tuple of (match: bool, details: dict with comparison info)
        """
        # Read files
        content1 = self.read_file(file1)
        content2 = self.read_file(file2)

        # Store original line counts
        orig_lines1 = content1.split('\n')
        orig_lines2 = content2.split('\n')

        # Normalize contents
        norm1 = self.normalizer.normalize(content1)
        norm2 = self.normalizer.normalize(content2)

        # Split into lines
        lines1 = norm1.split('\n')
        lines2 = norm2.split('\n')

        # Compare
        is_match = norm1 == norm2

        # Calculate similarity
        similarity = SequenceMatcher(None, norm1, norm2).ratio()

        # Generate diff if not matching
        diff_lines = []
        if not is_match:
            diff = unified_diff(
                lines1,
                lines2,
                fromfile=f'{Path(file1).name} (normalized)',
                tofile=f'{Path(file2).name} (normalized)',
                lineterm='',
                n=3
            )
            diff_lines = list(diff)

        return is_match, {
            'file1': file1,
            'file2': file2,
            'original_lines_1': len(orig_lines1),
            'original_lines_2': len(orig_lines2),
            'normalized_lines_1': len(lines1),
            'normalized_lines_2': len(lines2),
            'similarity': similarity,
            'diff_lines': diff_lines,
            'content1': norm1,
            'content2': norm2,
        }

    def generate_diff_output(self, diff_lines: List[str]) -> str:
        """Generate colored diff output."""
        output = []
        for line in diff_lines:
            if line.startswith('+++') or line.startswith('---'):
                output.append(self._colorize(line, 'blue'))
            elif line.startswith('+'):
                output.append(self._colorize(line, 'green'))
            elif line.startswith('-'):
                output.append(self._colorize(line, 'red'))
            elif line.startswith('@@'):
                output.append(self._colorize(line, 'yellow'))
            else:
                output.append(line)
        return '\n'.join(output)

    def count_differences(self, diff_lines: List[str]) -> int:
        """Count the number of actual differences (not context lines)."""
        count = 0
        for line in diff_lines:
            if line.startswith('+') or line.startswith('-'):
                if not line.startswith('+++') and not line.startswith('---'):
                    count += 1
        return count

    def print_report(self, is_match: bool, details: dict) -> None:
        """Print formatted comparison report."""
        file1_name = Path(details['file1']).name
        file2_name = Path(details['file2']).name

        print("\n" + "=" * 70)
        print("A/B Output Comparison Report (Phase 33.3)")
        print("=" * 70)

        print(f"\nFiles compared:")
        print(f"  File 1: {details['file1']}")
        print(f"  File 2: {details['file2']}")

        status = self._colorize("MATCH", 'green') if is_match else self._colorize("DIFFERENT", 'red')
        print(f"\nStatus: {status}")

        print(f"\nFile Statistics:")
        print(f"  {file1_name}:")
        print(f"    Original lines:     {details['original_lines_1']}")
        print(f"    Normalized lines:   {details['normalized_lines_1']}")
        print(f"  {file2_name}:")
        print(f"    Original lines:     {details['original_lines_2']}")
        print(f"    Normalized lines:   {details['normalized_lines_2']}")

        similarity_pct = details['similarity'] * 100
        print(f"\nSimilarity: {similarity_pct:.2f}%")

        if not is_match:
            diff_count = self.count_differences(details['diff_lines'])
            print(f"Differences: {diff_count} changes")

            if self.verbose:
                print("\n" + "-" * 70)
                print("Unified Diff (normalized content):")
                print("-" * 70)
                diff_output = self.generate_diff_output(details['diff_lines'])
                print(diff_output)
        else:
            print(f"\nDifferences: 0")

        print("\n" + "=" * 70)

    def main(self, args: Optional[List[str]] = None) -> int:
        """Main entry point."""
        parser = argparse.ArgumentParser(
            description='Compare C++ transpiler outputs (C vs CPP) for A/B testing',
            formatter_class=argparse.RawDescriptionHelpFormatter,
            epilog="""
Examples:
  python3 compare.py cpp_output.txt c_output.txt
  python3 compare.py output1.c output2.c --verbose
  python3 compare.py result_cpp.txt result_c.txt --no-ignore-comments
            """
        )

        parser.add_argument(
            'file1',
            help='First output file (C++ version)'
        )
        parser.add_argument(
            'file2',
            help='Second output file (C version)'
        )
        parser.add_argument(
            '--verbose', '-v',
            action='store_true',
            help='Show detailed diff output'
        )
        parser.add_argument(
            '--no-ignore-comments',
            action='store_true',
            help='Do not ignore comment differences'
        )
        parser.add_argument(
            '--no-color',
            action='store_true',
            help='Disable colored output'
        )

        parsed_args = parser.parse_args(args)

        # Override verbose setting if requested
        self.verbose = parsed_args.verbose

        # Override color setting if requested
        if parsed_args.no_color:
            self.color_enabled = False

        # Perform comparison
        is_match, details = self.compare_files(
            parsed_args.file1,
            parsed_args.file2
        )

        # Print report
        self.print_report(is_match, details)

        # Return appropriate exit code
        return 0 if is_match else 1


def main():
    """Entry point for command-line usage."""
    comparator = OutputComparator()
    sys.exit(comparator.main())


if __name__ == '__main__':
    main()
