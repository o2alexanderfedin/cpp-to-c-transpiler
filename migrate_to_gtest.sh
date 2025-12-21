#!/bin/bash
#
# Migrate integration test files to Google Test framework
#

set -e

migrate_file() {
    local file="$1"
    local backup="${file}.backup_$(date +%Y%m%d_%H%M%S)"

    echo "Migrating: $file"

    # Create backup
    cp "$file" "$backup"

    # Create a temporary file for our transformations
    local tmp_file=$(mktemp)

    # Step 1: Add GTest header if not present
    if ! grep -q '#include <gtest/gtest.h>' "$file"; then
        sed -i '' '1i\
// Migrated to Google Test Framework\
' "$file"

        # Find first #include and insert gtest before it
        sed -i '' '/^#include/ {
            i\
#include <gtest/gtest.h>

            :a
            n
            ba
        }' "$file" 2>/dev/null || true
    fi

    # Step 2: Remove old test framework code
    sed -i '' '/^static int tests_passed/d' "$file"
    sed -i '' '/^static int tests_failed/d' "$file"

    # Step 3: Remove macro definitions
    sed -i '' '/^#define TEST_START/d' "$file"
    sed -i '' '/^#define TEST_PASS/d' "$file"
    sed -i '' '/^#define TEST_FAIL/d' "$file"

    # Step 4: Remove multi-line ASSERT macros (more complex)
    perl -i -p0e 's/#define ASSERT\(.*?\n.*?\n.*?\n.*?\n//gs' "$file"
    perl -i -p0e 's/#define ASSERT_CONTAINS\(.*?\n.*?\n.*?\n.*?\n//gs' "$file"
    perl -i -p0e 's/#define ASSERT_NOT_EMPTY\(.*?\n.*?\n.*?\n//gs' "$file"

    # Step 5: Convert void test_xxx() to TEST(Suite, Name)
    # This is complex, so we'll do it with Perl
    perl -i -pe '
        s/^void (test_\w+)\s*\(\)\s*\{/sub convert_name {
            my $name = shift;
            $name =~ s\/^test_\/\/;
            my @parts = split(/_/, $name);
            return join("", map { ucfirst($_) } @parts);
        }
        "TEST(IntegrationTest, " . convert_name($1) . ") {"/e' "$file"

    # Step 6: Remove TEST_START calls
    sed -i '' '/TEST_START(/d' "$file"

    # Step 7: Remove TEST_PASS calls
    sed -i '' '/TEST_PASS(/d' "$file"

    # Step 8: Convert ASSERT() calls to EXPECT_TRUE()
    sed -i '' 's/ASSERT(\([^,]*\), *"\([^"]*\)")/EXPECT_TRUE(\1) << "\2"/g' "$file"

    # Step 9: Convert ASSERT_CONTAINS
    perl -i -pe 's/ASSERT_CONTAINS\(([^,]+),\s*([^,]+),\s*"([^"]+)"\)/EXPECT_NE($1.find($2), std::string::npos) << "$3"/g' "$file"

    # Step 10: Convert ASSERT_NOT_EMPTY
    perl -i -pe 's/ASSERT_NOT_EMPTY\(([^,]+),\s*"([^"]+)"\)/EXPECT_FALSE($1.empty()) << "$2"/g' "$file"

    # Step 11: Replace main() function
    perl -i -p0e 's/int main\(\) \{.*?return.*?;.*?\}/int main(int argc, char **argv) {\n    ::testing::InitGoogleTest(\&argc, \&argv);\n    return RUN_ALL_TESTS();\n}/gs' "$file"

    echo "Migrated: $file (backup at $backup)"
}

# Main execution
if [ $# -eq 0 ]; then
    echo "Usage: $0 <test_file> [test_file2 ...]"
    echo "Example: $0 tests/ExceptionHandlingIntegrationTest.cpp"
    exit 1
fi

for file in "$@"; do
    if [ ! -f "$file" ]; then
        echo "Error: File not found: $file"
        continue
    fi
    migrate_file "$file"
done

echo "Migration complete!"
