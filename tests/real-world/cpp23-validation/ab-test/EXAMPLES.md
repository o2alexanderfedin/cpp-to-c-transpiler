# Usage Examples - A/B Output Comparison Tool

## Basic Comparisons

### Example 1: Simple Match Test
```bash
$ python3 compare.py ref.c transpiled.c
```

Expected output for matching files:
```
======================================================================
A/B Output Comparison Report (Phase 33.3)
======================================================================

Files compared:
  File 1: ref.c
  File 2: transpiled.c

Status: MATCH

File Statistics:
  ref.c:
    Original lines:     45
    Normalized lines:   42
  transpiled.c:
    Original lines:     47
    Normalized lines:   42

Similarity: 100.00%

Differences: 0

======================================================================
```

Exit code: `0` (success)

---

## Detailed Comparisons

### Example 2: Finding Differences
```bash
$ python3 compare.py old.cpp new.cpp --verbose
```

Output when files differ:
```
======================================================================
A/B Output Comparison Report (Phase 33.3)
======================================================================

Files compared:
  File 1: old.cpp
  File 2: new.cpp

Status: DIFFERENT

File Statistics:
  old.cpp:
    Original lines:     50
    Normalized lines:   48
  new.cpp:
    Original lines:     51
    Normalized lines:   48

Similarity: 98.30%
Differences: 3 changes

----------------------------------------------------------------------
Unified Diff (normalized content):
----------------------------------------------------------------------
--- old.cpp (normalized)
+++ new.cpp (normalized)
@@ -15,8 +15,9 @@
 struct Data {
     int id;
     char* name;
+    int status;
 };

 void process_data(struct Data* data) {
```

Exit code: `1` (failure)

---

## Advanced Use Cases

### Example 3: Comparing With Comments Considered
```bash
$ python3 compare.py file1.c file2.c --no-ignore-comments
```

This will show differences in comments as well:
```
Status: DIFFERENT
Differences: 2 changes
```

Instead of treating comment-only differences as insignificant.

---

### Example 4: Batch Testing in Shell Script
```bash
#!/bin/bash
# ab-test-suite.sh - Run A/B tests on multiple files

COMPARE_SCRIPT="./compare.py"
FAILED=0

test_pair() {
    local file1=$1
    local file2=$2
    local test_name=$3

    echo "Testing: $test_name"

    if $COMPARE_SCRIPT "$file1" "$file2" --no-color > /tmp/test_result.txt 2>&1; then
        echo "  PASS: $test_name"
        return 0
    else
        echo "  FAIL: $test_name"
        echo "  Details:"
        $COMPARE_SCRIPT "$file1" "$file2" --verbose --no-color | head -20
        ((FAILED++))
        return 1
    fi
}

# Run multiple tests
test_pair "output/test1_cpp.txt" "output/test1_c.txt" "Vector Test"
test_pair "output/test2_cpp.txt" "output/test2_c.txt" "String Test"
test_pair "output/test3_cpp.txt" "output/test3_c.txt" "Class Test"

echo ""
echo "Test Summary: $((3 - FAILED))/3 passed"
exit $FAILED
```

---

### Example 5: CI/CD Integration
```yaml
# .github/workflows/ab-test.yml
name: A/B Output Comparison

on: [push, pull_request]

jobs:
  ab-test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Set up Python
        uses: actions/setup-python@v2
        with:
          python-version: '3.x'

      - name: Run transpiler
        run: ./build-transpiler.sh

      - name: Compare outputs
        run: |
          python3 tests/real-world/cpp23-validation/ab-test/compare.py \
            build/output_cpp.txt \
            build/output_c.txt
```

---

### Example 6: Finding Specific Differences
```bash
$ python3 compare.py v1.c v2.c --verbose | grep "@@" -A 10
```

Shows only the specific changed sections with context.

---

### Example 7: Detailed Analysis Report
```bash
#!/bin/bash
# Create detailed comparison report

echo "=== A/B Testing Report ===" > report.txt
echo "Generated: $(date)" >> report.txt
echo "" >> report.txt

for test in tests/*.cpp; do
    base=$(basename "$test" .cpp)
    echo "Test: $base" >> report.txt

    python3 compare.py \
        "output/${base}_cpp.c" \
        "output/${base}_c.c" \
        --verbose --no-color >> report.txt 2>&1

    echo "---" >> report.txt
    echo "" >> report.txt
done

echo "Report saved to: report.txt"
```

---

## Handling Common Scenarios

### Floating Point Differences
Files with slightly different floating-point representations:
```bash
$ python3 compare.py result1.txt result2.txt
# Outputs will be normalized: 1.500000 and 1.5 are treated equivalently
```

---

### Different Whitespace
C++ version:
```c
int main()
{
    int x = 10;    // extra spaces


    return 0;
}
```

C version:
```c
int main()
{
    int x = 10;
    return 0;
}
```

```bash
$ python3 compare.py cpp_ver.c c_ver.c
Status: MATCH  # Because whitespace is normalized
```

---

### Platform Line Ending Differences
```bash
# Windows (CRLF) vs Unix (LF) files will compare as MATCH
$ python3 compare.py windows.c unix.c
Status: MATCH
```

---

## Performance Examples

### Large File Comparison
```bash
$ time python3 compare.py large_file_1.c large_file_2.c

real    0m0.245s
user    0m0.198s
sys     0m0.041s
# Fast processing even for files with thousands of lines
```

---

### Piping Results
```bash
# Redirect output for logging
python3 compare.py output1.c output2.c --verbose --no-color > comparison.log 2>&1

# Extract only pass/fail for scripting
if python3 compare.py file1.c file2.c --no-color > /dev/null 2>&1; then
    echo "PASS"
else
    echo "FAIL"
fi
```

---

## Troubleshooting Examples

### Example: Finding Why Tests Fail
```bash
# First, check basic comparison
$ python3 compare.py a.c b.c
Status: DIFFERENT

# Then, see the details
$ python3 compare.py a.c b.c --verbose
# Shows exact lines that differ

# Then, check if it's just comments
$ python3 compare.py a.c b.c --no-ignore-comments --verbose
# If this shows more differences, it's comment-related
```

---

## Integration Examples

### With Make
```makefile
.PHONY: validate-ab-test
validate-ab-test:
	@echo "Running A/B validation..."
	@python3 tests/real-world/cpp23-validation/ab-test/compare.py \
		build/cpp_output.txt \
		build/c_output.txt \
		--verbose
	@echo "A/B validation passed!"
```

### With CMake
```cmake
add_test(
    NAME ABTestComparison
    COMMAND python3
    ${PROJECT_SOURCE_DIR}/tests/real-world/cpp23-validation/ab-test/compare.py
    ${CMAKE_BINARY_DIR}/output_cpp.txt
    ${CMAKE_BINARY_DIR}/output_c.txt
)
```

---

## Summary

These examples demonstrate:
- ✓ Basic comparisons for quality assurance
- ✓ Detailed diff analysis for debugging
- ✓ Batch testing in scripts
- ✓ CI/CD integration patterns
- ✓ Report generation
- ✓ Performance characteristics
- ✓ Integration with build systems

For more details, see `README.md` or `QUICK_START.md`.
