# Scripts Directory

This directory contains utility scripts for the cpptoc project.

## Available Scripts

### Code Coverage

#### generate_coverage.sh

Generates comprehensive code coverage reports for the project.

**Quick Start:**
```bash
./scripts/generate_coverage.sh
```

**Options:**
- `--clean` - Clean build directory before building
- `--build-dir DIR` - Specify build directory (default: build-coverage)
- `--output-dir DIR` - Specify output directory (default: coverage)
- `--verbose` - Enable verbose output
- `--help` - Show help message

**Requirements:**
- lcov (install with: `brew install lcov` on macOS)
- CMake 3.20+
- C++17 compiler with gcov support

**What it does:**
1. Configures CMake with coverage enabled (-DENABLE_COVERAGE=ON)
2. Builds all test executables with instrumentation
3. Runs all 492 test functions (1,956 assertions)
4. Collects coverage data using lcov
5. Generates HTML and summary reports

**Output:**
- HTML report: `build-coverage/coverage/index.html`
- Coverage data: `build-coverage/coverage.info.cleaned`

#### view_coverage.sh

Opens and displays code coverage reports.

**Quick Start:**
```bash
./scripts/view_coverage.sh
```

**Options:**
- `--build-dir DIR` - Specify build directory (default: build-coverage)
- `--output-dir DIR` - Specify output directory (default: coverage)
- `--summary` - Show coverage summary in terminal
- `--text` - Generate text coverage report
- `--no-browser` - Don't open browser
- `--help` - Show help message

**Examples:**
```bash
# Open HTML report in browser
./scripts/view_coverage.sh

# Show summary in terminal
./scripts/view_coverage.sh --summary

# Generate text report without opening browser
./scripts/view_coverage.sh --text --no-browser
```

### Build Optimization

#### optimize_build.sh

Optimizes build configuration and settings.

#### test_memory_leaks.sh

Tests for memory leaks in the transpiler.

### GitHub Projects

The `gh-projects/` subdirectory contains scripts for GitHub project management integration.

## Usage Workflow

### Typical Development Workflow

1. **Make code changes**
2. **Run tests and coverage**:
   ```bash
   ./scripts/generate_coverage.sh --clean
   ```
3. **View results**:
   ```bash
   ./scripts/view_coverage.sh --summary
   ```
4. **Review HTML report** (opens automatically)
5. **Address uncovered code** as needed

### CI/CD Integration

For automated testing:
```bash
./scripts/generate_coverage.sh --clean --verbose
./scripts/view_coverage.sh --summary --text --no-browser
```

## Coverage Targets

The project aims for:
- **Line Coverage**: 80%+
- **Function Coverage**: 85%+
- **Branch Coverage**: 75%+

## Troubleshooting

### "lcov: not found"

Install lcov:
```bash
# macOS
brew install lcov

# Ubuntu/Debian
sudo apt-get install lcov

# Fedora/RHEL
sudo dnf install lcov
```

### "No coverage data found"

Run the generate script first:
```bash
./scripts/generate_coverage.sh
```

### Tests failing during coverage

Enable verbose mode to see detailed output:
```bash
./scripts/generate_coverage.sh --verbose
```

## More Information

For detailed testing and coverage documentation, see [docs/TESTING.md](/docs/TESTING.md).
