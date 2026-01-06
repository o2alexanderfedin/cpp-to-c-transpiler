#!/bin/bash
# Bug #25 Workaround: Post-process generated C to fix scoped enum references
# This is a temporary fix until proper AST translation is implemented

# Fix scoped enum references: TokenType::Value -> Value
find transpiled -name "*.c" -o -name "*.h" | while read file; do
    # Fix TokenType:: scoped references
    sed -i '' 's/TokenType::\([A-Za-z_][A-Za-z0-9_]*\)/\1/g' "$file"
done

echo "Fixed scoped enum references in generated C code"
