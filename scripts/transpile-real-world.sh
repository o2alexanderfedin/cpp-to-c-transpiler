#!/usr/bin/env bash

################################################################################
# Transpile Real-World Test Projects
#
# This script transpiles all 5 real-world C++ test projects to C using the
# transpiler-api-cli tool and organizes the output in a mirrored directory
# structure under tests/real-world/transpiled/
#
# Projects:
#   - json-parser
#   - logger
#   - resource-manager
#   - string-formatter
#   - test-framework
################################################################################

set -euo pipefail

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRANSPILER="${PROJECT_ROOT}/build_working/transpiler-api-cli"
SOURCE_DIR="${PROJECT_ROOT}/tests/real-world"
TARGET_DIR="${PROJECT_ROOT}/tests/real-world/transpiled"
LOG_DIR="${PROJECT_ROOT}/test-logs"
LOG_FILE="${LOG_DIR}/transpile-real-world.log"
TIMESTAMP=$(date +"%Y-%m-%d %H:%M:%S")

# Statistics
TOTAL_FILES=0
SUCCESS_COUNT=0
FAILURE_COUNT=0
TOTAL_LOC=0

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Projects to transpile
PROJECTS=(
    "json-parser"
    "logger"
    "resource-manager"
    "string-formatter"
    "test-framework"
)

################################################################################
# Functions
################################################################################

log() {
    echo -e "$1" | tee -a "$LOG_FILE"
}

log_info() {
    log "${BLUE}[INFO]${NC} $1"
}

log_success() {
    log "${GREEN}[SUCCESS]${NC} $1"
}

log_error() {
    log "${RED}[ERROR]${NC} $1"
}

log_warning() {
    log "${YELLOW}[WARNING]${NC} $1"
}

# Check if transpiler exists
check_transpiler() {
    if [[ ! -x "$TRANSPILER" ]]; then
        log_error "Transpiler not found at: $TRANSPILER"
        log_info "Please build the project first: cd build_working && make"
        exit 1
    fi
    log_success "Transpiler found at: $TRANSPILER"
}

# Create necessary directories
setup_directories() {
    log_info "Setting up directories..."
    mkdir -p "$LOG_DIR"

    # Clean target directory (remove all existing transpiled files)
    log_info "Cleaning target directory: $TARGET_DIR"
    if [[ -d "$TARGET_DIR" ]]; then
        # Remove everything except .gitkeep files
        find "$TARGET_DIR" -mindepth 1 ! -name '.gitkeep' -exec rm -rf {} + 2>/dev/null || true
    fi
    mkdir -p "$TARGET_DIR"

    log_success "Directory setup complete"
}

# Initialize log file
init_log() {
    cat > "$LOG_FILE" << EOF
================================================================================
Real-World Test Projects Transpilation Log
================================================================================
Timestamp: $TIMESTAMP
Transpiler: $TRANSPILER
Source: $SOURCE_DIR
Target: $TARGET_DIR
Projects: ${PROJECTS[*]}
================================================================================

EOF
}

# Count lines of code in a file
count_loc() {
    local file="$1"
    if [[ -f "$file" ]]; then
        # Count non-empty, non-comment lines
        grep -v "^\s*$" "$file" | grep -v "^\s*//" | wc -l | tr -d ' '
    else
        echo "0"
    fi
}

# Extract JSON field from transpiler output
extract_json_field() {
    local json_output="$1"
    local field="$2"

    # Extract the JSON object (everything after the last { before the field)
    local json_block=$(echo "$json_output" | sed -n '/{/,/}/p' | tail -n +$(echo "$json_output" | grep -n "^{" | tail -1 | cut -d: -f1))

    # Use Python to properly parse JSON
    python3 -c "
import json
import sys
try:
    data = json.loads('''$json_block''')
    value = data.get('$field', '')
    if isinstance(value, bool):
        print('true' if value else 'false')
    elif isinstance(value, list):
        print(json.dumps(value))
    else:
        print(value)
except Exception as e:
    sys.stderr.write(f'JSON parse error: {e}\n')
    sys.exit(1)
"
}

# Transpile a single file
transpile_file() {
    local source_file="$1"
    local project="$2"
    local relative_path="$3"

    TOTAL_FILES=$((TOTAL_FILES + 1))

    log_info "Transpiling [$TOTAL_FILES]: $relative_path"

    # Determine output paths
    local filename=$(basename "$source_file")
    local base_name="${filename%.*}"
    local extension="${filename##*.}"
    local dir_path=$(dirname "$relative_path")

    # Create target directory
    local target_dir="$TARGET_DIR/$project/$dir_path"
    mkdir -p "$target_dir"

    # Run transpiler with JSON output
    local transpiler_output
    if ! transpiler_output=$("$TRANSPILER" "$source_file" --json 2>&1); then
        log_error "Transpiler failed for: $relative_path"
        echo "$transpiler_output" >> "$LOG_FILE"
        FAILURE_COUNT=$((FAILURE_COUNT + 1))
        return 1
    fi

    # Extract JSON output (skip debug messages)
    local json_output=$(echo "$transpiler_output" | sed -n '/{/,/}/p' | tail -n +$(echo "$transpiler_output" | grep -n "^{" | tail -1 | cut -d: -f1 2>/dev/null || echo "1"))

    # Check success status
    local success=$(extract_json_field "$json_output" "success" 2>/dev/null || echo "false")

    if [[ "$success" != "true" ]]; then
        log_error "Transpilation failed for: $relative_path"
        echo "=== Transpiler Output ===" >> "$LOG_FILE"
        echo "$transpiler_output" >> "$LOG_FILE"
        echo "=== JSON Output ===" >> "$LOG_FILE"
        echo "$json_output" >> "$LOG_FILE"
        echo "" >> "$LOG_FILE"
        FAILURE_COUNT=$((FAILURE_COUNT + 1))
        return 1
    fi

    # Extract C and H code
    local c_code=$(extract_json_field "$json_output" "c" 2>/dev/null || echo "")
    local h_code=$(extract_json_field "$json_output" "h" 2>/dev/null || echo "")

    # Write C file (always for .cpp files)
    if [[ "$extension" == "cpp" ]]; then
        local c_file="$target_dir/${base_name}.c"
        echo "$c_code" > "$c_file"
        local loc=$(count_loc "$c_file")
        TOTAL_LOC=$((TOTAL_LOC + loc))
        log_success "  -> C file: $c_file (${loc} LOC)"
    fi

    # Write H file if content exists
    if [[ -n "$h_code" && "$h_code" != '""' && "$h_code" != "null" ]]; then
        local h_file="$target_dir/${base_name}.h"
        echo "$h_code" > "$h_file"
        log_success "  -> H file: $h_file"
    fi

    # Copy original header files to transpiled directory (they might be needed)
    if [[ "$extension" == "h" ]]; then
        local h_file="$target_dir/${filename}"
        cp "$source_file" "$h_file"
        log_success "  -> Header copied: $h_file"
    fi

    SUCCESS_COUNT=$((SUCCESS_COUNT + 1))
    return 0
}

# Transpile all files in a project
transpile_project() {
    local project="$1"
    local project_dir="$SOURCE_DIR/$project"

    log_info ""
    log_info "========================================="
    log_info "Transpiling project: $project"
    log_info "========================================="

    if [[ ! -d "$project_dir" ]]; then
        log_error "Project directory not found: $project_dir"
        return 1
    fi

    # Find all .cpp and .h files (excluding build directories)
    local files=()
    while IFS= read -r -d '' file; do
        files+=("$file")
    done < <(find "$project_dir" \( -name "*.cpp" -o -name "*.h" \) ! -path "*/build/*" ! -path "*/transpiled/*" -print0)

    if [[ ${#files[@]} -eq 0 ]]; then
        log_warning "No source files found in: $project"
        return 0
    fi

    log_info "Found ${#files[@]} files in $project"

    # Transpile each file
    for file in "${files[@]}"; do
        local relative_path="${file#$project_dir/}"
        transpile_file "$file" "$project" "$relative_path"
    done

    log_success "Project $project complete"
}

# Generate summary report
generate_summary() {
    local summary_file="$LOG_DIR/transpile-summary.txt"
    local success_rate=0

    if [[ $TOTAL_FILES -gt 0 ]]; then
        success_rate=$(awk "BEGIN {printf \"%.1f\", ($SUCCESS_COUNT / $TOTAL_FILES) * 100}")
    fi

    cat > "$summary_file" << EOF
================================================================================
Real-World Test Projects Transpilation Summary
================================================================================
Timestamp: $TIMESTAMP
Duration: $(date +"%Y-%m-%d %H:%M:%S")

Projects Processed: ${#PROJECTS[@]}
  - json-parser
  - logger
  - resource-manager
  - string-formatter
  - test-framework

File Statistics:
  Total Files:       $TOTAL_FILES
  Successful:        $SUCCESS_COUNT
  Failed:            $FAILURE_COUNT
  Success Rate:      ${success_rate}%

Code Statistics:
  Total LOC:         $TOTAL_LOC

Output Directory:
  $TARGET_DIR

Log Files:
  Detailed log:      $LOG_FILE
  Summary:           $summary_file

================================================================================
EOF

    # Display summary
    log_info ""
    log_info "========================================="
    log_info "TRANSPILATION SUMMARY"
    log_info "========================================="
    log_info "Total Files:       $TOTAL_FILES"
    log_success "Successful:        $SUCCESS_COUNT"
    if [[ $FAILURE_COUNT -gt 0 ]]; then
        log_error "Failed:            $FAILURE_COUNT"
    else
        log_success "Failed:            $FAILURE_COUNT"
    fi
    log_info "Success Rate:      ${success_rate}%"
    log_info "Total LOC:         $TOTAL_LOC"
    log_info ""
    log_success "Summary saved to: $summary_file"
    log_success "Detailed log at: $LOG_FILE"
}

################################################################################
# Main Execution
################################################################################

main() {
    log_info "Starting Real-World Test Projects Transpilation"
    log_info "================================================"

    # Pre-flight checks
    check_transpiler
    setup_directories
    init_log

    # Transpile each project
    for project in "${PROJECTS[@]}"; do
        transpile_project "$project"
    done

    # Generate summary
    generate_summary

    # Exit code based on results
    if [[ $FAILURE_COUNT -gt 0 ]]; then
        log_warning "Transpilation completed with $FAILURE_COUNT failures"
        exit 0  # Still exit 0 as partial success is acceptable
    else
        log_success "All files transpiled successfully!"
        exit 0
    fi
}

# Run main function
main "$@"
