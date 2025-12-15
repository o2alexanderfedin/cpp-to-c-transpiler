#!/usr/bin/env python3
"""
Update all references to gh-projects scripts in markdown files
to include the .sh extension.
"""

import os
import re
import sys
from pathlib import Path

# Script names that were renamed (without .sh extension)
SCRIPT_NAMES = [
    'gh-project-convert',
    'gh-project-create',
    'gh-project-delete',
    'gh-project-init',
    'gh-project-item-complete',
    'gh-project-item-create',
    'gh-project-item-get-acceptance-criteria',
    'gh-project-item-start',
    'gh-project-item-view',
    'gh-project-link',
    'gh-project-link-repo',
    'gh-project-list',
    'gh-project-setup-apply',
    'gh-project-setup-clone',
    'gh-project-setup-init',
    'gh-project-update',
]

def update_file_references(file_path, script_names):
    """Update script references in a single markdown file."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return 0

    original_content = content
    replacements = 0

    for script_name in script_names:
        # Create patterns to match script references
        # Pattern 1: Bare script name with word boundaries
        # Use negative lookahead to avoid replacing if .sh already present
        pattern1 = re.compile(
            r'\b' + re.escape(script_name) + r'(?!\.sh)\b'
        )

        # Count matches
        matches = pattern1.findall(content)
        if matches:
            replacements += len(matches)
            # Replace with .sh extension
            content = pattern1.sub(script_name + '.sh', content)

    # Only write if content changed
    if content != original_content:
        try:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            return replacements
        except Exception as e:
            print(f"Error writing {file_path}: {e}")
            return 0

    return 0


def main():
    skills_dir = Path.home() / '.claude' / 'skills'

    if not skills_dir.exists():
        print(f"Error: Skills directory not found: {skills_dir}")
        sys.exit(1)

    # Find all markdown files
    md_files = list(skills_dir.rglob('*.md'))

    print(f"Found {len(md_files)} markdown files to process")
    print()

    total_files_modified = 0
    total_replacements = 0
    modified_files = []

    for md_file in sorted(md_files):
        replacements = update_file_references(md_file, SCRIPT_NAMES)
        if replacements > 0:
            total_files_modified += 1
            total_replacements += replacements
            modified_files.append(str(md_file))
            print(f"Updated {md_file.relative_to(skills_dir)}: {replacements} reference(s)")

    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Total markdown files processed: {len(md_files)}")
    print(f"Total files modified: {total_files_modified}")
    print(f"Total references updated: {total_replacements}")
    print()

    if modified_files:
        print("Modified files:")
        for file_path in modified_files:
            print(f"  - {file_path}")
        print()

    print("Update completed successfully!")


if __name__ == '__main__':
    main()
