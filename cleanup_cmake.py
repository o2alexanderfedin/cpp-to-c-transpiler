#!/usr/bin/env python3
"""
Script to comment out non-essential build targets from CMakeLists.txt
Keeps: cpptoc_core, test_fixtures, all unit tests, all E2E tests
Removes: Main executables, integration tests, subdirectories
"""

import re
from pathlib import Path

# Define targets to DELETE
DELETE_EXECUTABLES = {
    'cpptoc',
    'transpiler-api-cli',
    'test_transpiler_api',
    'test_transpiler_complex',
}

DELETE_INTEGRATION_TESTS = {
    'STLIntegrationTest',
    'AdvancedTemplateIntegrationTest',
    'RuntimeIntegrationTest',
    'ConsoleAppTest',
    'HeaderCompatibilityTest',
    'IntegrationTest',
    'RAIIIntegrationTest',
    'VirtualFunctionIntegrationTest',
    'ExceptionIntegrationTest',
    'CoroutineIntegrationTest',
    'VirtualMethodIntegrationTest',
    'StaticMemberIntegrationTest',
    'HandlerIntegrationTest',
    'ControlFlowIntegrationTest',
    'GlobalVariablesIntegrationTest',
    'PointersIntegrationTest',
    'StructsIntegrationTest',
    'ExceptionThreadSafetyTest',
    'ExceptionPerformanceTest',
    'TranspilerAPI_VirtualFiles_Test',
    'TranspilerAPI_HeaderSeparation_Test',
    'TranspilerAPI_MutualStructReferences_Test',
    'MultiFileTranspilationTest',
}

# E2E tests to KEEP
KEEP_E2E_TESTS = {
    'E2EPhase1Test',
    'ControlFlowE2ETest',
    'GlobalVariablesE2ETest',
    'PointersE2ETest',
    'StructsE2ETest',
    'ClassesE2ETest',
    'MultipleInheritanceE2ETest',
    'EnumE2ETest',
    'Phase61ModuleRejectionTest',
}

DELETE_SUBDIRECTORIES = {
    'tests/helpers',
    'tests/real-world/json-parser',
    'tests/real-world/resource-manager',
    'tests/real-world/logger',
    'tests/real-world/string-formatter',
    'tests/real-world/test-framework',
}

# All targets to delete
ALL_DELETE_TARGETS = DELETE_EXECUTABLES | DELETE_INTEGRATION_TESTS

def should_delete_target(target_name):
    """Check if target should be deleted"""
    return target_name in ALL_DELETE_TARGETS

def process_cmake_file(input_path, output_path):
    """Process CMakeLists.txt and comment out unwanted targets"""

    with open(input_path, 'r') as f:
        lines = f.readlines()

    output_lines = []
    in_delete_block = False
    delete_target_name = None
    block_start_line = 0
    deleted_targets = []
    deleted_subdirs = []
    lines_commented = 0

    i = 0
    while i < len(lines):
        line = lines[i]

        # Check for add_subdirectory to delete
        subdir_match = re.match(r'^add_subdirectory\((.*?)\)', line)
        if subdir_match:
            subdir = subdir_match.group(1)
            if subdir in DELETE_SUBDIRECTORIES:
                output_lines.append(f'# DELETED: Subdirectory - {subdir}\n')
                output_lines.append(f'# {line}')
                deleted_subdirs.append(subdir)
                lines_commented += 1
                i += 1
                continue

        # Check for add_executable to delete
        exec_match = re.match(r'^add_executable\(([\w_-]+)', line)
        if exec_match:
            target_name = exec_match.group(1)
            if should_delete_target(target_name):
                in_delete_block = True
                delete_target_name = target_name
                block_start_line = i
                deleted_targets.append(target_name)

                # Determine the reason
                if target_name in DELETE_EXECUTABLES:
                    reason = "Main executable"
                else:
                    reason = "Integration test"

                output_lines.append(f'# DELETED: {reason} - {target_name}\n')
                output_lines.append(f'# {line}')
                lines_commented += 1
                i += 1

                # Continue commenting until we find the closing paren of add_executable
                paren_depth = 1 if '(' in line and ')' not in line else 0
                while i < len(lines) and paren_depth > 0:
                    line = lines[i]
                    if '(' in line:
                        paren_depth += line.count('(')
                    if ')' in line:
                        paren_depth -= line.count(')')
                    output_lines.append(f'# {line}')
                    lines_commented += 1
                    i += 1
                # Now we're past the add_executable, stay in delete block for target_* commands
                continue

        # If we're in a delete block, comment out the line
        if in_delete_block:
            # Check if this line belongs to the target we're deleting
            # Target blocks include: target_compile_definitions, target_include_directories, target_link_libraries, gtest_discover_tests

            # Check for gtest_discover_tests for this target
            if re.match(r'^gtest_discover_tests\(' + re.escape(delete_target_name), line):
                # This is the gtest registration for our target - comment it out
                output_lines.append(f'# {line}')
                lines_commented += 1
                i += 1
                # Continue commenting until we find the closing paren
                paren_depth = 1 if '(' in line and ')' not in line else 0
                while i < len(lines) and paren_depth > 0:
                    line = lines[i]
                    if '(' in line:
                        paren_depth += 1
                    if ')' in line:
                        paren_depth -= 1
                    output_lines.append(f'# {line}')
                    lines_commented += 1
                    i += 1
                # End of gtest block, end target deletion
                in_delete_block = False
                delete_target_name = None
                continue

            # Check if this is a target_* command for our target
            target_cmd_match = re.match(r'^(target_\w+|set_target_properties)\(' + re.escape(delete_target_name), line)
            if target_cmd_match:
                # Comment out this target command and all its lines until closing paren
                output_lines.append(f'# {line}')
                lines_commented += 1
                i += 1
                paren_depth = 1 if '(' in line and ')' not in line else 0
                while i < len(lines) and paren_depth > 0:
                    line = lines[i]
                    if '(' in line:
                        paren_depth += 1
                    if ')' in line:
                        paren_depth -= 1
                    output_lines.append(f'# {line}')
                    lines_commented += 1
                    i += 1
                continue

            # Check for end of target block
            # End when we hit: new target, section separator, or non-target command
            is_end = False
            if line.strip() == '':
                # Blank line might signal end, but check next non-blank line
                output_lines.append(line)
                i += 1
                continue
            elif re.match(r'^add_executable\(', line):
                # New target starts
                is_end = True
            elif re.match(r'^add_library\(', line):
                # New library starts
                is_end = True
            elif re.match(r'^# ={3,}', line):
                # Section separator
                is_end = True
            elif not re.match(r'^(target_|gtest_discover_tests|set_target_properties|#)', line):
                # Line that doesn't belong to target configuration
                is_end = True

            if is_end:
                in_delete_block = False
                delete_target_name = None
                # Don't comment this line, it's the start of next section
                output_lines.append(line)
                i += 1
                continue

            # Comment out the line (it's part of the target block)
            if not line.startswith('#'):
                output_lines.append(f'# {line}')
                lines_commented += 1
            else:
                output_lines.append(line)
            i += 1
            continue

        # Normal line, keep it
        output_lines.append(line)
        i += 1

    # Write output
    with open(output_path, 'w') as f:
        f.writelines(output_lines)

    return {
        'deleted_targets': sorted(deleted_targets),
        'deleted_subdirs': sorted(deleted_subdirs),
        'lines_commented': lines_commented,
    }

def main():
    input_file = Path('/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/CMakeLists.txt')
    output_file = Path('/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/CMakeLists.txt.new')

    result = process_cmake_file(input_file, output_file)

    print("=" * 80)
    print("CMakeLists.txt Cleanup Summary")
    print("=" * 80)
    print(f"\nLines commented out: {result['lines_commented']}")
    print(f"\nDeleted targets ({len(result['deleted_targets'])}):")
    for target in result['deleted_targets']:
        print(f"  - {target}")
    print(f"\nDeleted subdirectories ({len(result['deleted_subdirs'])}):")
    for subdir in result['deleted_subdirs']:
        print(f"  - {subdir}")
    print("\nOutput written to: CMakeLists.txt.new")
    print("Please review and then replace CMakeLists.txt if correct.")

if __name__ == '__main__':
    main()
