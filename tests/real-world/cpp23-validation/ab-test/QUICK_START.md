# Quick Start Guide - A/B Output Comparison Tool

## One-Minute Overview

The `compare.py` script compares C++ transpiler outputs with intelligent normalization, perfect for Phase 33.3 A/B testing.

## Installation

```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/cpp23-validation/ab-test
chmod +x compare.py  # Already done
```

## Basic Command

```bash
python3 compare.py file1.txt file2.txt
```

## Common Scenarios

### 1. Compare two transpiler outputs
```bash
python3 compare.py cpp_output.txt c_output.txt
```

### 2. See what's different (with diffs)
```bash
python3 compare.py output1.c output2.c --verbose
```

### 3. Include comment differences
```bash
python3 compare.py file1.txt file2.txt --no-ignore-comments
```

### 4. Disable colors for piping/logging
```bash
python3 compare.py file1.txt file2.txt --no-color
```

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Files match (pass) |
| 1 | Files differ (fail) |
| 2 | Error (missing file, etc) |

## Features at a Glance

✓ Normalizes whitespace (strips trailing spaces, collapses blank lines)
✓ Ignores platform differences (CRLF vs LF)
✓ Strips comments by default (C++ and C style)
✓ Highlights differences with unified diff
✓ Shows similarity percentage
✓ Color output for terminals
✓ Fast processing of large files

## Example Output

```
======================================================================
A/B Output Comparison Report (Phase 33.3)
======================================================================

Files compared:
  File 1: output1.c
  File 2: output2.c

Status: MATCH

File Statistics:
  output1.c:
    Original lines:     123
    Normalized lines:   120
  output2.c:
    Original lines:     125
    Normalized lines:   120

Similarity: 99.50%
Differences: 0

======================================================================
```

## Troubleshooting

**"Error: File not found"**
- Check the file path and name are correct
- Use absolute paths: `/path/to/file.txt`

**"Status: DIFFERENT" but files look the same**
- Use `--verbose` to see exact differences
- Could be trailing spaces, extra blank lines, or numeric formatting

**Want to see every difference, including comments?**
- Add `--no-ignore-comments` flag

**Colors not showing?**
- Your terminal might not support ANSI colors
- Use `--no-color` flag if they interfere

## Architecture at a Glance

```
OutputNormalizer: Cleans up text
  ↓
OutputComparator: Compares files
  ↓
Report generation: User-friendly output
  ↓
Exit with code (0/1/2)
```

## Full Documentation

See `README.md` for comprehensive documentation including:
- Detailed normalization process
- Integration with CI/CD
- Performance notes
- Implementation details
- Use cases and examples

## Development Notes

- **Language**: Python 3
- **Lines of code**: 323
- **Classes**: 2 (OutputNormalizer, OutputComparator)
- **Key methods**: compare_files(), print_report(), normalize()
- **Dependencies**: Python standard library only (no external packages)
- **SOLID principles**: Followed throughout
