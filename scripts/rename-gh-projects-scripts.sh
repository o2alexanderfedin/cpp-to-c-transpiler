#!/bin/bash
#
# Script to rename all gh-projects shell scripts to have .sh extension
# and update all references in markdown files
#
# Usage: ./scripts/rename-gh-projects-scripts.sh
#

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Counters
SCRIPTS_FOUND=0
SCRIPTS_RENAMED=0
MD_FILES_CHECKED=0
MD_FILES_MODIFIED=0
TOTAL_REFERENCES_UPDATED=0

# Arrays to track changes
declare -a RENAMED_SCRIPTS
declare -a MODIFIED_MD_FILES

# Directory paths
SKILLS_DIR="$HOME/.claude/skills"
GH_PROJECTS_DIR="$SKILLS_DIR/lib/gh-projects"

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}GitHub Projects Scripts Renaming Tool${NC}"
echo -e "${BLUE}========================================${NC}"
echo

# ============================================================================
# PHASE 1: DISCOVERY
# ============================================================================
echo -e "${YELLOW}Phase 1: Discovery${NC}"
echo "Scanning for scripts in: $GH_PROJECTS_DIR"
echo

# Find all files without .sh extension (excluding directories, README.md, and files already with extensions)
SCRIPTS_TO_RENAME=()
while IFS= read -r line; do
    SCRIPTS_TO_RENAME+=("$line")
done < <(find "$GH_PROJECTS_DIR" -maxdepth 1 -type f ! -name "*.sh" ! -name "*.md" | sort)

SCRIPTS_FOUND=${#SCRIPTS_TO_RENAME[@]}

if [ $SCRIPTS_FOUND -eq 0 ]; then
    echo -e "${GREEN}No scripts found to rename. All scripts already have .sh extension.${NC}"
    exit 0
fi

echo "Found $SCRIPTS_FOUND script(s) to rename:"
for script in "${SCRIPTS_TO_RENAME[@]}"; do
    basename "$script"
done
echo

# Find all markdown files
MD_FILES=()
while IFS= read -r line; do
    MD_FILES+=("$line")
done < <(find "$SKILLS_DIR" -name "*.md" -type f | sort)
MD_FILES_CHECKED=${#MD_FILES[@]}
echo "Found $MD_FILES_CHECKED markdown file(s) to check for references"
echo

# ============================================================================
# PHASE 2: VALIDATION
# ============================================================================
echo -e "${YELLOW}Phase 2: Validation${NC}"
echo

# Verify all files are shell scripts (have shebang or execute permission)
for script in "${SCRIPTS_TO_RENAME[@]}"; do
    if [ ! -x "$script" ]; then
        echo -e "${RED}WARNING: $script is not executable${NC}"
    fi

    # Check for shebang
    if ! head -n 1 "$script" | grep -q '^#!'; then
        echo -e "${YELLOW}WARNING: $script does not have a shebang${NC}"
    fi
done

# Check for naming conflicts
for script in "${SCRIPTS_TO_RENAME[@]}"; do
    new_name="${script}.sh"
    if [ -e "$new_name" ]; then
        echo -e "${RED}ERROR: Naming conflict - $new_name already exists!${NC}"
        exit 1
    fi
done

echo -e "${GREEN}Validation passed${NC}"
echo

# ============================================================================
# PHASE 3: RENAME SCRIPTS
# ============================================================================
echo -e "${YELLOW}Phase 3: Renaming Scripts${NC}"
echo

for script in "${SCRIPTS_TO_RENAME[@]}"; do
    old_name="$script"
    new_name="${script}.sh"
    old_basename=$(basename "$old_name")
    new_basename=$(basename "$new_name")

    echo -n "Renaming: $old_basename -> $new_basename ... "

    # Rename the file
    mv "$old_name" "$new_name"

    # Verify the rename succeeded
    if [ -f "$new_name" ] && [ ! -f "$old_name" ]; then
        # Verify executable permission is preserved
        if [ -x "$new_name" ]; then
            echo -e "${GREEN}OK${NC}"
            RENAMED_SCRIPTS+=("$old_basename -> $new_basename")
            ((SCRIPTS_RENAMED++))
        else
            echo -e "${RED}FAILED (lost executable permission)${NC}"
            exit 1
        fi
    else
        echo -e "${RED}FAILED${NC}"
        exit 1
    fi
done

echo
echo -e "${GREEN}Renamed $SCRIPTS_RENAMED script(s)${NC}"
echo

# ============================================================================
# PHASE 4: UPDATE REFERENCES
# ============================================================================
echo -e "${YELLOW}Phase 4: Updating References in Markdown Files${NC}"
echo

# Create a temporary directory for backup files
BACKUP_DIR=$(mktemp -d)
echo "Backup directory: $BACKUP_DIR"
echo

# Build sed patterns for each renamed script
declare -a SED_PATTERNS
for script in "${SCRIPTS_TO_RENAME[@]}"; do
    old_basename=$(basename "$script")
    new_basename="${old_basename}.sh"

    # Pattern 1: Bare script name with word boundaries
    # Use [[:<:]] and [[:>:]] for BSD sed (macOS)
    SED_PATTERNS+=("s|[[:<:]]${old_basename}[[:>:]]|${new_basename}|g")

    # Pattern 2: Script name in paths (with directory separators)
    SED_PATTERNS+=("s|/${old_basename}([^.])|/${new_basename}\1|g")
    SED_PATTERNS+=("s|/${old_basename}\$|/${new_basename}|g")
done

# Process each markdown file
for md_file in "${MD_FILES[@]}"; do
    md_basename=$(basename "$md_file")

    # Check if file contains any references to scripts being renamed
    file_has_references=false
    for script in "${SCRIPTS_TO_RENAME[@]}"; do
        old_basename=$(basename "$script")
        if grep -q "$old_basename" "$md_file" 2>/dev/null; then
            file_has_references=true
            break
        fi
    done

    if [ "$file_has_references" = false ]; then
        continue
    fi

    echo -n "Processing: $md_file ... "

    # Create backup
    cp "$md_file" "$BACKUP_DIR/$md_basename.backup"

    # Count references before update
    refs_before=0
    for script in "${SCRIPTS_TO_RENAME[@]}"; do
        old_basename=$(basename "$script")
        count=$(grep -o "$old_basename" "$md_file" 2>/dev/null | wc -l | tr -d ' ')
        refs_before=$((refs_before + count))
    done

    # Apply all sed patterns
    temp_file=$(mktemp)
    cp "$md_file" "$temp_file"

    for script in "${SCRIPTS_TO_RENAME[@]}"; do
        old_basename=$(basename "$script")
        new_basename="${old_basename}.sh"

        # Multiple strategies to catch all reference patterns

        # Strategy 1: Bare script name with word boundaries (BSD sed)
        sed -i '' "s/\(^\|[^a-zA-Z0-9_/.-]\)${old_basename}\([^a-zA-Z0-9_.-]\|$\)/\1${new_basename}\2/g" "$temp_file"

        # Strategy 2: Script name preceded by / (in paths)
        sed -i '' "s|/${old_basename}\([^a-zA-Z0-9_.-]\|$\)|/${new_basename}\1|g" "$temp_file"

        # Strategy 3: Script name in backticks or code blocks
        sed -i '' "s|\`${old_basename}\`|\`${new_basename}\`|g" "$temp_file"

        # Strategy 4: Script name at start of line
        sed -i '' "s|^${old_basename}\([^a-zA-Z0-9_.-]\|$\)|${new_basename}\1|g" "$temp_file"
    done

    # Count references after update
    refs_after=0
    for script in "${SCRIPTS_TO_RENAME[@]}"; do
        new_basename=$(basename "$script").sh
        count=$(grep -o "$new_basename" "$temp_file" 2>/dev/null | wc -l | tr -d ' ')
        refs_after=$((refs_after + count))
    done

    # Check if file was actually modified
    if ! cmp -s "$md_file" "$temp_file"; then
        mv "$temp_file" "$md_file"
        refs_updated=$refs_after
        TOTAL_REFERENCES_UPDATED=$((TOTAL_REFERENCES_UPDATED + refs_updated))
        echo -e "${GREEN}OK${NC} (updated $refs_updated reference(s))"
        MODIFIED_MD_FILES+=("$md_file")
        ((MD_FILES_MODIFIED++))
    else
        rm "$temp_file"
        echo -e "${YELLOW}SKIPPED${NC} (no changes needed)"
    fi
done

echo
echo -e "${GREEN}Updated references in $MD_FILES_MODIFIED markdown file(s)${NC}"
echo

# ============================================================================
# PHASE 5: VERIFICATION
# ============================================================================
echo -e "${YELLOW}Phase 5: Verification${NC}"
echo

# Verify all scripts now have .sh extension
echo "Checking for scripts without .sh extension..."
REMAINING=()
while IFS= read -r line; do
    REMAINING+=("$line")
done < <(find "$GH_PROJECTS_DIR" -maxdepth 1 -type f ! -name "*.sh" ! -name "*.md" 2>/dev/null || true)

if [ ${#REMAINING[@]} -gt 0 ] && [ -n "${REMAINING[0]}" ]; then
    echo -e "${RED}ERROR: Found scripts without .sh extension:${NC}"
    for script in "${REMAINING[@]}"; do
        echo "  - $(basename "$script")"
    done
    exit 1
else
    echo -e "${GREEN}All scripts have .sh extension${NC}"
fi

# Verify all scripts are still executable
echo "Verifying executable permissions..."
non_executable=0
for script in "${SCRIPTS_TO_RENAME[@]}"; do
    new_script="${script}.sh"
    if [ ! -x "$new_script" ]; then
        echo -e "${RED}ERROR: $new_script is not executable${NC}"
        ((non_executable++))
    fi
done

if [ $non_executable -eq 0 ]; then
    echo -e "${GREEN}All scripts are executable${NC}"
else
    exit 1
fi

# Check for remaining old-style references in markdown files
echo "Checking for remaining old-style references..."
remaining_refs_found=false

for script in "${SCRIPTS_TO_RENAME[@]}"; do
    old_basename=$(basename "$script")

    # Search for the old script name (without .sh) but exclude:
    # - References that are already part of the new name with .sh
    # - References in directory names
    # - Substring matches (use word boundaries)

    while IFS= read -r line; do
        # Skip lines that already have .sh extension
        if echo "$line" | grep -q "${old_basename}.sh"; then
            continue
        fi

        # Found a reference that wasn't updated
        if [ "$remaining_refs_found" = false ]; then
            echo -e "${YELLOW}WARNING: Found possible remaining references:${NC}"
            remaining_refs_found=true
        fi
        echo "  $line"
    done < <(grep -n "\b${old_basename}\b" "${MD_FILES[@]}" 2>/dev/null | grep -v "${old_basename}.sh" || true)
done

if [ "$remaining_refs_found" = false ]; then
    echo -e "${GREEN}No old-style references found${NC}"
fi

echo

# ============================================================================
# SUMMARY REPORT
# ============================================================================
echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}SUMMARY REPORT${NC}"
echo -e "${BLUE}========================================${NC}"
echo
echo "Scripts renamed: $SCRIPTS_RENAMED"
echo
if [ ${#RENAMED_SCRIPTS[@]} -gt 0 ]; then
    echo "Renamed scripts:"
    for entry in "${RENAMED_SCRIPTS[@]}"; do
        echo "  - $entry"
    done
    echo
fi

echo "Markdown files checked: $MD_FILES_CHECKED"
echo "Markdown files modified: $MD_FILES_MODIFIED"
echo "Total references updated: $TOTAL_REFERENCES_UPDATED"
echo

if [ ${#MODIFIED_MD_FILES[@]} -gt 0 ]; then
    echo "Modified markdown files:"
    for file in "${MODIFIED_MD_FILES[@]}"; do
        echo "  - $file"
    done
    echo
fi

echo "Backup directory: $BACKUP_DIR"
echo "(Backups will be automatically cleaned up after verification)"
echo

echo -e "${GREEN}========================================${NC}"
echo -e "${GREEN}RENAMING COMPLETED SUCCESSFULLY${NC}"
echo -e "${GREEN}========================================${NC}"
echo

exit 0
