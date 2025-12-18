# Benchmark Performance Regression Detection

This document describes the automated benchmark regression detection system integrated into the CI/CD pipeline.

## Overview

The benchmark regression detection system automatically runs performance benchmarks on every push to `develop` or `main` branches and on pull requests. It compares the current performance against a baseline and fails the build if performance degrades beyond a configurable threshold.

## Components

### 1. Benchmark Runner Script (`run_benchmarks.sh`)

The main script that executes all benchmarks and generates structured JSON output.

**Features:**
- Runs all transpiler component benchmarks
- Generates JSON reports with structured metrics
- Supports baseline mode for establishing performance baselines
- Supports comparison mode for detecting regressions

**Usage:**
```bash
# Run benchmarks and save as baseline
./benchmarks/run_benchmarks.sh --baseline

# Run benchmarks with comparison
./benchmarks/run_benchmarks.sh --compare baseline.json --ci

# Quick mode (fewer iterations for fast feedback)
./benchmarks/run_benchmarks.sh --quick
```

### 2. Comparison Script (`compare_benchmarks.py`)

Python script for detailed benchmark comparison and regression detection.

**Features:**
- Compares two benchmark JSON files
- Calculates percentage change for each metric
- Detects regressions based on configurable threshold
- Supports multiple output formats (text, JSON, markdown)
- CI mode with exit code 1 on regression

**Usage:**
```bash
# Compare benchmarks with 5% threshold
./benchmarks/compare_benchmarks.py baseline.json current.json --threshold 5.0

# Generate markdown report for PR comments
./benchmarks/compare_benchmarks.py baseline.json current.json --format markdown

# CI mode (fail on regression)
./benchmarks/compare_benchmarks.py baseline.json current.json --ci --threshold 5.0
```

### 3. GitHub Actions Workflow (`.github/workflows/benchmark-regression.yml`)

Automated CI/CD workflow that runs on every push and pull request.

**Features:**
- Builds project with benchmarks enabled
- Downloads previous baseline from artifacts
- Runs current benchmarks
- Compares against baseline
- Posts results as PR comment (for pull requests)
- Fails build if regression detected
- Uploads results as artifacts for future comparisons
- Tracks performance trends over time

**Workflow Triggers:**
- Push to `develop` or `main`
- Pull requests to `develop` or `main`
- Manual workflow dispatch

## Benchmark Metrics

The system tracks the following metrics for each benchmark:

### Transpiler Component Benchmarks

1. **AST Traversal Performance**
   - Measures: Time per traversal operation
   - Unit: nanoseconds (ns)
   - Lower is better

2. **Name Mangling Performance**
   - Measures: Time per name mangle operation
   - Unit: nanoseconds (ns)
   - Lower is better

3. **Code Generation Performance**
   - Measures: Time per code generation operation
   - Unit: nanoseconds (ns)
   - Lower is better

4. **End-to-End Transpilation**
   - Measures: Total transpilation time
   - Unit: milliseconds (ms)
   - Lower is better

5. **Memory Usage Profiling**
   - Measures: Peak memory usage
   - Unit: megabytes (MB)
   - Lower is better

6. **Virtual Function Resolution**
   - Measures: Time per virtual call resolution
   - Unit: nanoseconds (ns)
   - Lower is better

### Runtime Benchmarks

1. **RTTI Runtime Performance**
   - Measures: dynamic_cast overhead vs native C++
   - Target: 10-20% overhead

2. **Exception Handling Performance**
   - Measures: try-catch and throw-catch overhead
   - Target: 5-10% overhead (no throw), 15-25% (with throw)

3. **Virtual Call Performance**
   - Measures: vtable dispatch overhead
   - Target: 0-2% overhead

4. **Coroutine Performance**
   - Measures: resume/destroy overhead
   - Target: 5-15% overhead

## Regression Detection

### Threshold Configuration

The default regression threshold is **5%**. This means:
- Performance degradation > 5% triggers a regression warning
- Build fails in CI mode if any benchmark regresses > 5%

You can configure the threshold:
- **Per workflow run**: Manual workflow dispatch input
- **Per comparison**: `--threshold` flag on comparison script
- **Environment variable**: `REGRESSION_THRESHOLD=5.0`

### Status Determination

For each benchmark metric:
- **Improved**: Performance improved by > 0.5%
- **No Change**: Performance changed by < 0.5%
- **Regression**: Performance degraded by > 0.5%

Build fails if any metric shows regression > threshold.

## Baseline Management

### Establishing a Baseline

Baselines are automatically established on every push to `develop` or `main`:

```bash
# Run benchmarks and save as baseline
./benchmarks/run_benchmarks.sh --baseline
```

The baseline is stored as `benchmark-results/baseline.json` and uploaded as a GitHub Actions artifact.

### Updating the Baseline

Baselines are automatically updated on every successful push to tracked branches. Manual baseline updates:

1. Run benchmarks locally: `./benchmarks/run_benchmarks.sh --baseline`
2. Commit the baseline: `git add benchmark-results/baseline.json`
3. Push to repository

### Artifact Storage

- **Baseline**: Stored for 90 days
- **Full results**: Stored for 30 days per commit
- **Performance history**: Stored for 365 days

## CI Integration

### Pull Request Workflow

1. PR is created or updated
2. GitHub Actions triggers benchmark workflow
3. Workflow downloads baseline from target branch
4. Workflow runs benchmarks on PR code
5. Comparison is performed
6. Results posted as PR comment
7. Build fails if regression detected

### PR Comment Format

The workflow posts a markdown comment with:
- Benchmark comparison table
- Performance changes (% and absolute)
- Status indicators (✅ improved, ❌ regression, ➖ no change)
- Summary statistics
- Regression details (if any)

Example:
```markdown
## Benchmark Comparison Report

**Baseline:** `baseline.json`
**Current:** `current.json`
**Regression Threshold:** 5.0%

### Benchmark Results

| Benchmark | Baseline | Current | Change | Status |
|-----------|----------|---------|--------|--------|
| `ast_traversal:mean_time_ns` | 150.00 ns | 145.00 ns | -3.33% | ✅ improved |
| `name_mangling:mean_time_ns` | 80.00 ns | 88.00 ns | +10.00% | ❌ regression |

### Summary

- **Total benchmarks compared:** 6
- **Improvements:** 3
- **Regressions (>5.0%):** 1
- **New benchmarks:** 0
- **Missing benchmarks:** 0

### ❌ Performance Regression Detected

The following benchmarks show significant regression:
- **name_mangling:mean_time_ns**: +10.00% (80.00ns → 88.00ns)
```

## Local Development

### Running Benchmarks Locally

```bash
# Build project with benchmarks
cmake -B build -DBUILD_BENCHMARKS=ON
cmake --build build

# Run benchmarks
./benchmarks/run_benchmarks.sh

# Run with comparison
./benchmarks/run_benchmarks.sh --compare benchmark-results/baseline.json
```

### Testing the Comparison Script

```bash
# Create test baseline
./benchmarks/run_benchmarks.sh --baseline

# Make some code changes
# ... edit code ...

# Run benchmarks again
./benchmarks/run_benchmarks.sh

# Compare
./benchmarks/compare_benchmarks.py \
  benchmark-results/baseline.json \
  benchmark-results/benchmark_*.json \
  --format markdown
```

## Performance Optimization Workflow

1. **Establish baseline**: Run benchmarks on current main branch
2. **Make optimization**: Implement performance improvement
3. **Run benchmarks**: Compare against baseline
4. **Iterate**: Continue optimizing until goals met
5. **Update baseline**: Merge to main to establish new baseline

## Troubleshooting

### Workflow Fails with "No baseline found"

This is expected on first run. The workflow will:
1. Run benchmarks
2. Save results as baseline
3. Future runs will compare against this baseline

### False Positives

If you get false regression warnings:
1. Check if changes are expected
2. Verify system load during benchmark
3. Consider adjusting threshold
4. Run benchmarks multiple times for consistency

### Benchmark Variance

To reduce variance:
- Use `--quick` mode for faster iterations during development
- Run full benchmarks in CI (default)
- Ensure consistent CI runner environment
- Consider using self-hosted runners for more stable results

## Future Enhancements

Potential improvements to the system:

1. **Performance Trending**: Visualize performance over time
2. **Benchmark History UI**: Web dashboard for historical data
3. **Multiple Baseline Comparison**: Compare against multiple previous versions
4. **Automatic Bisection**: Identify exact commit that caused regression
5. **Performance Budget**: Set per-benchmark performance budgets
6. **Slack/Email Notifications**: Alert on regressions
7. **Benchmark Warmup**: Add warmup iterations to reduce variance

## References

- [Benchmark Suite Documentation](./README.md)
- [GitHub Actions Workflow](../.github/workflows/benchmark-regression.yml)
- [Comparison Script](./compare_benchmarks.py)
- [Runner Script](./run_benchmarks.sh)
