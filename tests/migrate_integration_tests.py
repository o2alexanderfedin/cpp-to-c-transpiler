#!/usr/bin/env python3
"""
Migration script for Integration Test files to Google Test framework.

Migrates from custom TEST_START/TEST_PASS/ASSERT macros to Google Test:
- TEST_START(name) → TEST_F(FixtureName, TestName)
- TEST_PASS(name) → (removed, implicit pass)
- ASSERT(expr, msg) → ASSERT_TRUE(expr) << msg
- Custom main() → Google Test main

Target files:
1. integration/FeatureInteractionTest.cpp (30 tests)
2. integration/FeatureCombinationTest.cpp (20 tests)
3. integration/EdgeCasesTest.cpp (30 tests)
4. integration/ErrorHandlingTest.cpp (25 tests)
5. ExceptionHandlingIntegrationTest.cpp (needs special handling)
6. OverloadResolutionTest.cpp (5 tests)
"""

import re
import sys
from pathlib import Path


def migrate_test_file(file_path: Path, fixture_name: str) -> tuple[bool, str]:
    """
    Migrate a single test file to Google Test format.

    Returns: (success, message)
    """
    try:
        content = file_path.read_text()
        original_content = content

        # Count tests before migration
        test_count = len(re.findall(r'void test_\w+\(\)', content))

        # Step 1: Replace includes
        content = re.sub(
            r'#include <iostream>\n#include <string>\n#include <vector>\n#include <memory>',
            '#include <gtest/gtest.h>\n#include <memory>\n#include <string>\n#include <vector>',
            content
        )

        # Step 2: Remove old test framework
        content = re.sub(
            r'// Test framework\n'
            r'static int tests_passed = 0;\n'
            r'static int tests_failed = 0;\n\n'
            r'#define TEST_START\(name\).*\n'
            r'#define TEST_PASS\(.*?\).*\n'
            r'#define TEST_FAIL\(.*?\).*\n'
            r'#define ASSERT\(expr, msg\).*\n',
            '',
            content
        )

        # Step 3: Add test fixture class
        helper_section = re.search(r'// Helper: Create AST from code', content)
        if helper_section:
            fixture_code = f"""
// Google Test Fixture
class {fixture_name} : public ::testing::Test {{
protected:
    std::unique_ptr<ASTUnit> createAST(const std::string &code, const std::string &filename = "test.cpp") {{
        std::vector<std::string> args = {{"-std=c++17"}};
        return clang::tooling::buildASTFromCodeWithArgs(code, args, filename);
    }}

    CXXRecordDecl* findClass(ASTContext &Ctx, const std::string &name) {{
        auto *TU = Ctx.getTranslationUnitDecl();
        for (auto *Decl : TU->decls()) {{
            if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {{
                if (RD->getNameAsString() == name) {{
                    return RD;
                }}
            }}
        }}
        return nullptr;
    }}
}};

"""
            content = content.replace('// Helper: Create AST from code\n', fixture_code + '// Helper: Create AST from code\n')

        # Step 4: Remove standalone helper functions that are now in fixture
        content = re.sub(
            r'std::unique_ptr<ASTUnit> createAST\(const std::string &code.*?\{.*?return AST;\n\}\n\n',
            '',
            content,
            flags=re.DOTALL
        )

        content = re.sub(
            r'// Helper: Find class by name\n'
            r'CXXRecordDecl\* findClass\(ASTContext &Ctx.*?\{.*?return nullptr;\n\}\n\n',
            '',
            content,
            flags=re.DOTALL
        )

        # Step 5: Convert test functions to TEST_F
        def convert_test_function(match):
            test_name = match.group(1)
            test_body = match.group(2)

            # Remove TEST_START
            test_body = re.sub(r'\s*TEST_START\(".*?"\);', '', test_body)

            # Remove TEST_PASS
            test_body = re.sub(r'\s*TEST_PASS\(".*?"\);', '', test_body)

            # Convert ASSERT to ASSERT_TRUE
            test_body = re.sub(
                r'ASSERT\(([^,]+),\s*"([^"]+)"\)',
                r'ASSERT_TRUE(\1) << "\2"',
                test_body
            )

            # Remove void return type (TEST_F doesn't need it)
            return f'TEST_F({fixture_name}, {test_name}) {{{test_body}}}'

        content = re.sub(
            r'void (test_\w+)\(\)\s*\{(.*?)\n\}',
            convert_test_function,
            content,
            flags=re.DOTALL
        )

        # Step 6: Replace main function with Google Test main
        main_pattern = r'int main\(\).*?\{.*?return tests_failed > 0 \? 1 : 0;\n\}'
        if re.search(main_pattern, content, re.DOTALL):
            content = re.sub(
                main_pattern,
                '''int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}''',
                content,
                flags=re.DOTALL
            )

        # Step 7: Remove old test output code
        content = re.sub(
            r'\s*std::cout << "\\n";\n'
            r'\s*std::cout << "=*".*?\n'
            r'.*?std::cout << "=*".*?\n',
            '',
            content
        )

        content = re.sub(
            r'\s*std::cout << "Category.*?\n'
            r'\s*std::cout << "-*".*?\n',
            '',
            content
        )

        content = re.sub(
            r'\s*std::cout << "Results:.*?\n'
            r'\s*std::cout << "=*".*?\n',
            '',
            content
        )

        # Step 8: Remove test function calls from main
        content = re.sub(r'\s*test_\w+\(\);', '', content)

        # Write back only if content changed
        if content != original_content:
            file_path.write_text(content)
            return (True, f"Migrated {test_count} tests")
        else:
            return (False, "No changes needed")

    except Exception as e:
        return (False, f"Error: {str(e)}")


def main():
    """Main migration function."""
    base_path = Path(__file__).parent

    # Files to migrate with their fixture names
    files_to_migrate = [
        ("integration/FeatureInteractionTest.cpp", "FeatureInteractionTest"),
        ("integration/FeatureCombinationTest.cpp", "FeatureCombinationTest"),
        ("integration/EdgeCasesTest.cpp", "EdgeCasesTest"),
        ("integration/ErrorHandlingTest.cpp", "ErrorHandlingTest"),
    ]

    print("=" * 70)
    print("Integration Test Migration to Google Test")
    print("=" * 70)

    total_tests = 0
    success_count = 0

    for file_rel_path, fixture_name in files_to_migrate:
        file_path = base_path / file_rel_path
        print(f"\nMigrating: {file_rel_path}")
        print(f"  Fixture: {fixture_name}")

        if not file_path.exists():
            print(f"  ✗ File not found: {file_path}")
            continue

        success, message = migrate_test_file(file_path, fixture_name)

        if success:
            print(f"  ✓ {message}")
            success_count += 1
            # Extract test count from message
            match = re.search(r'(\d+) tests', message)
            if match:
                total_tests += int(match.group(1))
        else:
            print(f"  ✗ {message}")

    print("\n" + "=" * 70)
    print(f"Summary: {success_count}/{len(files_to_migrate)} files migrated")
    print(f"Total tests migrated: {total_tests}")
    print("=" * 70)

    return 0 if success_count == len(files_to_migrate) else 1


if __name__ == "__main__":
    sys.exit(main())
