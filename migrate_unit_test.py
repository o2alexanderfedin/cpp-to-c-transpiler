#!/usr/bin/env python3
"""
Automated migration script for unit tests from HandlerContext to UnitTestContext
"""
import sys
import re

def migrate_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    original = content

    # 1. Replace includes
    content = content.replace(
        '#include "handlers/HandlerContext.h"',
        '#include "helpers/UnitTestHelper.h"'
    )

    # 2. Replace class members - more robust pattern
    pattern = r'protected:\s+std::unique_ptr<clang::ASTUnit> cppAST;\s+std::unique_ptr<clang::ASTUnit> cAST;\s+std::unique_ptr<clang::CNodeBuilder> builder;\s+std::unique_ptr<HandlerContext> context;\s+std::unique_ptr<(\w+)> handler;'

    match = re.search(pattern, content)
    if match:
        handler_type = match.group(1)
        content = re.sub(
            pattern,
            f'protected:\n    UnitTestContext ctx;',
            content
        )

        # 3. Replace SetUp() method
        setup_pattern = r'void SetUp\(\) override \{[^}]+builder = std::make_unique[^}]+handler = std::make_unique<' + handler_type + r'>\(\);\s+\}'
        content = re.sub(
            setup_pattern,
            f'void SetUp() override {{\n        ctx = createUnitTestContext();\n        ctx.dispatcher->registerHandler<{handler_type}>();\n    }}',
            content,
            flags=re.DOTALL
        )

        # 4. Remove TearDown() method
        content = re.sub(
            r'\s+void TearDown\(\) override \{[^}]+\}',
            '',
            content,
            flags=re.DOTALL
        )

        # 5. Determine mapper based on handler type
        if 'Expression' in handler_type:
            mapper = 'exprMapper'
            handle_method = 'handleExpr'
        elif 'Statement' in handler_type:
            mapper = 'stmtMapper'
            handle_method = 'handleStmt'
        else:
            mapper = 'declMapper'
            handle_method = 'handleDecl'

        # 6. Replace handler->handleXXX calls
        content = re.sub(
            rf'handler->{handle_method}\((\w+), \*context\)',
            lambda m: f'ctx.dispatcher->dispatch({m.group(1)});\n    auto result = ctx.{mapper}->get({m.group(1)}); result',
            content
        )

        print(f"✓ Migrated {filepath}")
        print(f"  Handler: {handler_type}")
        print(f"  Mapper: ctx.{mapper}")

        if content != original:
            with open(filepath, 'w') as f:
                f.write(content)
            return True
    else:
        print(f"✗ Could not detect handler pattern in {filepath}")
        return False

    return False

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: python3 migrate_unit_test.py <file>")
        sys.exit(1)

    filepath = sys.argv[1]
    migrate_file(filepath)
