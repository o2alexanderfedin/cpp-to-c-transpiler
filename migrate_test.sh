#!/bin/bash
# Automated migration script for unit tests from HandlerContext to UnitTestContext

FILE="$1"
if [ -z "$FILE" ]; then
    echo "Usage: $0 <test-file-path>"
    exit 1
fi

echo "Migrating: $FILE"

# Backup
cp "$FILE" "${FILE}.bak"

# 1. Replace include
sed -i '' 's|#include "handlers/HandlerContext.h"|#include "helpers/UnitTestHelper.h"|g' "$FILE"

# 2. Replace class members (more robust pattern)
perl -i -pe 'BEGIN{undef $/;} s/protected:\s*std::unique_ptr<clang::ASTUnit> cppAST;\s*std::unique_ptr<clang::ASTUnit> cAST;\s*std::unique_ptr<clang::CNodeBuilder> builder;\s*std::unique_ptr<HandlerContext> context;/protected:\n    UnitTestContext ctx;/smg' "$FILE"

# 3. Detect which handler is used
HANDLER_TYPE=$(grep -oE "(Expression|Statement|Record|Constructor|Destructor|Method|Variable|Enum)Handler" "$FILE" | head -1)

if [ -z "$HANDLER_TYPE" ]; then
    echo "Could not detect handler type"
    exit 1
fi

echo "Detected handler: $HANDLER_TYPE"

# Determine mapper
case "$HANDLER_TYPE" in
    ExpressionHandler)
        MAPPER="exprMapper"
        ;;
    StatementHandler)
        MAPPER="stmtMapper"
        ;;
    RecordHandler|ConstructorHandler|DestructorHandler|MethodHandler|VariableHandler|EnumHandler)
        MAPPER="declMapper"
        ;;
    *)
        echo "Unknown handler type: $HANDLER_TYPE"
        exit 1
        ;;
esac

echo "Using mapper: $MAPPER"

# Done
echo "Migration complete for: $FILE"
echo "Handler: $HANDLER_TYPE"
echo "Mapper: ctx.$MAPPER"
