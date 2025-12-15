#!/bin/bash
set -euo pipefail

# ============================================================================
# Comprehensive Script Reference Updater for gh-projects Scripts
# ============================================================================
# This script ensures:
# 1. All scripts in ~/.claude/skills/lib/gh-projects/ have .sh extension
# 2. ALL references across ALL markdown files (recursively) are updated
# 3. Complete verification with detailed reporting
# ============================================================================

# ANSI color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# Configuration
SCRIPTS_DIR="$HOME/.claude/skills/lib/gh-projects"
SKILLS_DIR="$HOME/.claude/skills"
TEMP_DIR=$(mktemp -d)
REPORT_FILE="${TEMP_DIR}/update_report.txt"

# Counters
total_scripts=0
renamed_scripts=0
total_md_files=0
processed_md_files=0
modified_md_files=0
total_references_updated=0

# Arrays to track changes
declare -a modified_files
declare -a script_mappings

# Cleanup on exit
trap 'rm -rf "$TEMP_DIR"' EXIT

# ============================================================================
# Helper Functions
# ============================================================================

log_section() {
    echo -e "\n${BLUE}========================================${NC}"
    echo -e "${BLUE}$1${NC}"
    echo -e "${BLUE}========================================${NC}\n"
}

log_info() {
    echo -e "${CYAN}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# ============================================================================
# Phase 1: Discovery & Current State Assessment
# ============================================================================

phase1_discovery() {
    log_section "PHASE 1: Discovery & Current State Assessment"

    # Check if directories exist
    if [[ ! -d "$SCRIPTS_DIR" ]]; then
        log_error "Scripts directory not found: $SCRIPTS_DIR"
        exit 1
    fi

    if [[ ! -d "$SKILLS_DIR" ]]; then
        log_error "Skills directory not found: $SKILLS_DIR"
        exit 1
    fi

    # List all scripts in gh-projects directory
    log_info "Scanning scripts in: $SCRIPTS_DIR"
    local scripts_with_sh=0
    local scripts_without_sh=0

    while IFS= read -r -d '' file; do
        ((total_scripts++))
        local basename=$(basename "$file")

        # Skip directories, lib subdirectory, templates directory, and .md files
        if [[ -d "$file" ]] || [[ "$basename" == "lib" ]] || [[ "$basename" == "templates" ]] || [[ "$basename" == *.md ]]; then
            continue
        fi

        if [[ "$basename" == *.sh ]]; then
            ((scripts_with_sh++))
        else
            ((scripts_without_sh++))
            echo "$basename" >> "${TEMP_DIR}/scripts_to_rename.txt"
        fi
    done < <(find "$SCRIPTS_DIR" -maxdepth 1 -type f -print0)

    log_info "Scripts with .sh extension: $scripts_with_sh"
    log_info "Scripts without .sh extension: $scripts_without_sh"

    # Find all markdown files recursively
    log_info "Finding all markdown files in: $SKILLS_DIR"
    find "$SKILLS_DIR" -type f -name "*.md" > "${TEMP_DIR}/all_md_files.txt"
    total_md_files=$(wc -l < "${TEMP_DIR}/all_md_files.txt" | tr -d ' ')
    log_info "Found $total_md_files markdown files to process"

    # Display directory structure depth
    local max_depth=$(find "$SKILLS_DIR" -type f -name "*.md" -exec dirname {} \; | awk -F'/' '{print NF}' | sort -rn | head -1)
    log_info "Maximum directory depth: $max_depth levels"

    echo ""
}

# ============================================================================
# Phase 2: Script Validation (if renaming needed)
# ============================================================================

phase2_validation() {
    log_section "PHASE 2: Script Validation"

    if [[ ! -f "${TEMP_DIR}/scripts_to_rename.txt" ]] || [[ ! -s "${TEMP_DIR}/scripts_to_rename.txt" ]]; then
        log_success "All scripts already have .sh extension - no renaming needed"
        return 0
    fi

    log_info "Validating scripts that need renaming..."

    while IFS= read -r script_name; do
        local script_path="${SCRIPTS_DIR}/${script_name}"

        # Verify it's a shell script
        if ! file "$script_path" | grep -q "shell script"; then
            log_warning "File may not be a shell script: $script_name"
        fi

        # Check for naming conflicts
        if [[ -f "${script_path}.sh" ]]; then
            log_error "Naming conflict: ${script_name}.sh already exists"
            exit 1
        fi

        # Verify write permissions
        if [[ ! -w "$script_path" ]]; then
            log_error "No write permission for: $script_name"
            exit 1
        fi

        log_info "✓ Validated: $script_name"
    done < "${TEMP_DIR}/scripts_to_rename.txt"

    log_success "All scripts validated successfully"
    echo ""
}

# ============================================================================
# Phase 3: Script Renaming (if needed)
# ============================================================================

phase3_rename_scripts() {
    log_section "PHASE 3: Script Renaming"

    if [[ ! -f "${TEMP_DIR}/scripts_to_rename.txt" ]] || [[ ! -s "${TEMP_DIR}/scripts_to_rename.txt" ]]; then
        log_success "No scripts need renaming"
        return 0
    fi

    log_info "Renaming scripts to add .sh extension..."

    while IFS= read -r script_name; do
        local old_path="${SCRIPTS_DIR}/${script_name}"
        local new_path="${old_path}.sh"

        # Rename the file
        mv "$old_path" "$new_path"

        # Verify renamed file exists
        if [[ ! -f "$new_path" ]]; then
            log_error "Failed to rename: $script_name"
            exit 1
        fi

        # Ensure it's executable
        chmod +x "$new_path"

        # Record the mapping
        echo "${script_name} -> ${script_name}.sh" >> "${TEMP_DIR}/rename_mappings.txt"
        script_mappings+=("${script_name}:${script_name}.sh")

        ((renamed_scripts++))
        log_success "Renamed: $script_name -> ${script_name}.sh"
    done < "${TEMP_DIR}/scripts_to_rename.txt"

    log_success "Renamed $renamed_scripts scripts"
    echo ""
}

# ============================================================================
# Phase 4: Comprehensive Reference Updates
# ============================================================================

phase4_update_references() {
    log_section "PHASE 4: Comprehensive Reference Updates"

    # Define all script names (without .sh extension)
    local script_names=(
        "gh-project-convert"
        "gh-project-create"
        "gh-project-delete"
        "gh-project-init"
        "gh-project-item-complete"
        "gh-project-item-create"
        "gh-project-item-get-acceptance-criteria"
        "gh-project-item-start"
        "gh-project-item-view"
        "gh-project-link"
        "gh-project-link-repo"
        "gh-project-list"
        "gh-project-setup-apply"
        "gh-project-setup-clone"
        "gh-project-setup-init"
        "gh-project-update"
    )

    log_info "Processing $total_md_files markdown files..."
    echo ""

    local file_count=0
    while IFS= read -r md_file; do
        ((file_count++))
        ((processed_md_files++))

        # Show progress every 10 files
        if ((file_count % 10 == 0)); then
            log_info "Progress: $file_count/$total_md_files files processed..."
        fi

        local file_modified=false
        local references_in_file=0

        # Create a temporary file for modifications
        local temp_file="${TEMP_DIR}/temp_md_file.txt"
        cp "$md_file" "$temp_file"

        # Process each script name
        for script_name in "${script_names[@]}"; do
            # Check if file contains this script name without .sh
            if grep -q "$script_name" "$temp_file"; then
                # Use sed with word boundaries for surgical precision
                # BSD sed (macOS) uses [[:<:]] and [[:>:]] for word boundaries
                local sed_pattern="s|\(\[\[:alnum:\]_-\]\)*${script_name}\([^.a-zA-Z0-9_-]\)|\1${script_name}.sh\2|g"

                # Try to update - use different approach for BSD sed
                # First, check for occurrences that need updating
                local old_count=$(grep -o "${script_name}[^.a-zA-Z0-9_-]" "$temp_file" 2>/dev/null | wc -l | tr -d ' ')

                if [[ $old_count -gt 0 ]]; then
                    # Use a more precise sed command for BSD sed
                    # Match script name followed by non-extension character
                    sed -i '' "s|\(^\|[^.a-zA-Z0-9_-]\)${script_name}\([^.a-zA-Z0-9_-]\)|\1${script_name}.sh\2|g" "$temp_file"

                    # Also catch end-of-line cases
                    sed -i '' "s|\(^\|[^.a-zA-Z0-9_-]\)${script_name}\$|\1${script_name}.sh|g" "$temp_file"

                    # Verify changes were made
                    local new_count=$(grep -o "${script_name}[^.a-zA-Z0-9_-]" "$temp_file" 2>/dev/null | wc -l | tr -d ' ')
                    local updated=$((old_count - new_count))

                    if [[ $updated -gt 0 ]]; then
                        references_in_file=$((references_in_file + updated))
                        file_modified=true
                    fi
                fi
            fi
        done

        # If file was modified, save it back
        if [[ "$file_modified" == true ]]; then
            cp "$temp_file" "$md_file"
            ((modified_md_files++))
            total_references_updated=$((total_references_updated + references_in_file))

            # Get relative path for reporting
            local rel_path="${md_file#$SKILLS_DIR/}"
            modified_files+=("$rel_path ($references_in_file refs)")

            echo "$rel_path: $references_in_file references updated" >> "${TEMP_DIR}/modified_files_detail.txt"
        fi

    done < "${TEMP_DIR}/all_md_files.txt"

    log_success "Processed all $processed_md_files markdown files"
    log_success "Modified $modified_md_files files"
    log_success "Updated $total_references_updated total references"
    echo ""
}

# ============================================================================
# Phase 5: Deep Verification
# ============================================================================

phase5_verification() {
    log_section "PHASE 5: Deep Verification"

    # Verify all scripts have .sh extension
    log_info "Verifying all scripts have .sh extension..."
    local scripts_without_sh=$(find "$SCRIPTS_DIR" -maxdepth 1 -type f ! -name "*.sh" ! -name "*.md" | wc -l | tr -d ' ')

    if [[ $scripts_without_sh -eq 0 ]]; then
        log_success "✓ All scripts have .sh extension"
    else
        log_error "✗ Found $scripts_without_sh scripts without .sh extension"
        find "$SCRIPTS_DIR" -maxdepth 1 -type f ! -name "*.sh" ! -name "*.md"
    fi

    # Verify all scripts are executable
    log_info "Verifying all scripts are executable..."
    local non_executable=$(find "$SCRIPTS_DIR" -maxdepth 1 -type f -name "*.sh" ! -perm +111 | wc -l | tr -d ' ')

    if [[ $non_executable -eq 0 ]]; then
        log_success "✓ All scripts are executable"
    else
        log_error "✗ Found $non_executable non-executable scripts"
        find "$SCRIPTS_DIR" -maxdepth 1 -type f -name "*.sh" ! -perm +111
    fi

    # Search for any remaining old-style references
    log_info "Searching for remaining old-style references..."
    local old_refs_found=0

    # Define pattern for old-style references (script name without .sh)
    local search_pattern='\(gh-project-convert\|gh-project-create\|gh-project-delete\|gh-project-init\|gh-project-item-complete\|gh-project-item-create\|gh-project-item-get-acceptance-criteria\|gh-project-item-start\|gh-project-item-view\|gh-project-link\|gh-project-link-repo\|gh-project-list\|gh-project-setup-apply\|gh-project-setup-clone\|gh-project-setup-init\|gh-project-update\)[^.a-zA-Z0-9_-]'

    if find "$SKILLS_DIR" -type f -name "*.md" -exec grep -l "$search_pattern" {} + > "${TEMP_DIR}/files_with_old_refs.txt" 2>/dev/null; then
        old_refs_found=$(wc -l < "${TEMP_DIR}/files_with_old_refs.txt" | tr -d ' ')
    fi

    if [[ $old_refs_found -eq 0 ]]; then
        log_success "✓ No old-style references found"
    else
        log_warning "⚠ Found potential old-style references in $old_refs_found files"
        log_info "Files with potential old-style references:"
        cat "${TEMP_DIR}/files_with_old_refs.txt" | while read -r file; do
            echo "  - ${file#$SKILLS_DIR/}"
        done
    fi

    echo ""
}

# ============================================================================
# Generate Final Report
# ============================================================================

generate_report() {
    log_section "FINAL REPORT"

    {
        echo "============================================================================"
        echo "COMPREHENSIVE GH-PROJECTS SCRIPT REFERENCE UPDATE REPORT"
        echo "============================================================================"
        echo ""
        echo "Generated: $(date)"
        echo ""

        echo "SUMMARY STATISTICS"
        echo "-------------------------------------------"
        echo "Total scripts in gh-projects/: $total_scripts"
        echo "Scripts renamed: $renamed_scripts"
        echo "Total markdown files found: $total_md_files"
        echo "Markdown files processed: $processed_md_files"
        echo "Markdown files modified: $modified_md_files"
        echo "Total references updated: $total_references_updated"
        echo ""

        if [[ $renamed_scripts -gt 0 ]]; then
            echo "SCRIPT RENAMING"
            echo "-------------------------------------------"
            if [[ -f "${TEMP_DIR}/rename_mappings.txt" ]]; then
                cat "${TEMP_DIR}/rename_mappings.txt"
            fi
            echo ""
        fi

        echo "ALL SCRIPTS IN GH-PROJECTS DIRECTORY"
        echo "-------------------------------------------"
        ls -1 "$SCRIPTS_DIR"/*.sh 2>/dev/null | while read -r script; do
            local basename=$(basename "$script")
            local perms=$(ls -l "$script" | awk '{print $1}')
            echo "  $basename [$perms]"
        done
        echo ""

        if [[ $modified_md_files -gt 0 ]]; then
            echo "MODIFIED MARKDOWN FILES (by directory)"
            echo "-------------------------------------------"
            if [[ -f "${TEMP_DIR}/modified_files_detail.txt" ]]; then
                # Group by directory
                sort "${TEMP_DIR}/modified_files_detail.txt" | while read -r line; do
                    echo "  $line"
                done
            fi
            echo ""
        fi

        echo "VERIFICATION RESULTS"
        echo "-------------------------------------------"
        local scripts_without_sh=$(find "$SCRIPTS_DIR" -maxdepth 1 -type f ! -name "*.sh" ! -name "*.md" 2>/dev/null | wc -l | tr -d ' ')
        echo "Scripts without .sh extension: $scripts_without_sh"

        local non_executable=$(find "$SCRIPTS_DIR" -maxdepth 1 -type f -name "*.sh" ! -perm +111 2>/dev/null | wc -l | tr -d ' ')
        echo "Non-executable scripts: $non_executable"

        echo ""
        echo "DIRECTORY COVERAGE"
        echo "-------------------------------------------"
        find "$SKILLS_DIR" -type d | while read -r dir; do
            local md_count=$(find "$dir" -maxdepth 1 -type f -name "*.md" 2>/dev/null | wc -l | tr -d ' ')
            if [[ $md_count -gt 0 ]]; then
                echo "  ${dir#$SKILLS_DIR/}: $md_count markdown files"
            fi
        done
        echo ""

        echo "============================================================================"

    } | tee "$REPORT_FILE"

    log_success "Report saved to: $REPORT_FILE"

    # Also save to current directory
    local final_report="./gh-projects-update-report.txt"
    cp "$REPORT_FILE" "$final_report"
    log_success "Report also saved to: $final_report"
}

# ============================================================================
# Main Execution
# ============================================================================

main() {
    echo -e "${CYAN}"
    echo "╔═══════════════════════════════════════════════════════════════════════╗"
    echo "║  Comprehensive GH-Projects Script Reference Updater                  ║"
    echo "║  Recursively updating ALL markdown files in ~/.claude/skills/         ║"
    echo "╚═══════════════════════════════════════════════════════════════════════╝"
    echo -e "${NC}"

    phase1_discovery
    phase2_validation
    phase3_rename_scripts
    phase4_update_references
    phase5_verification
    generate_report

    echo ""
    log_section "COMPLETION"

    if [[ $modified_md_files -gt 0 ]]; then
        log_success "Successfully updated $total_references_updated references across $modified_md_files files"
    else
        log_info "No references needed updating - all files already use correct .sh extension"
    fi

    log_success "All operations completed successfully!"
    echo ""
}

# Run main function
main

exit 0
