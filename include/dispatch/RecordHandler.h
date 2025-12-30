/**
 * @file RecordHandler.h
 * @brief Handler for processing RecordDecl nodes (struct/class declarations)
 *
 * Registers with CppToCVisitorDispatcher to handle C++ struct and class declarations.
 * Translates C++ structs/classes to C struct declarations with field translation.
 *
 * Phase 1 Scope: Structure translation ONLY
 * - Struct/class name and tag normalization (class → struct)
 * - Field translation (dispatch types via TypeHandler)
 * - Nested struct flattening (Outer__Inner pattern with double underscore)
 * - Forward declarations vs complete definitions
 *
 * Phase 3: NameMangler Integration
 * - Uses NameMangler::mangleClassName for all class/struct name mangling
 * - Removed custom getMangledName() - replaced by NameMangler
 * - Consistent with InstanceMethodHandler and StaticMethodHandler
 *
 * Future Phases:
 * - Methods translation (CXXMethodDecl → static functions)
 * - Polymorphism support (vtables)
 * - Inheritance (flatten to single struct with base fields)
 * - Access specifiers (not applicable in C)
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"

namespace cpptoc {

/**
 * @class RecordHandler
 * @brief Processes RecordDecl (struct/class) and creates C struct declarations
 *
 * Responsibilities:
 * - Match RecordDecl nodes (predicate) - struct and class (CXXRecordDecl)
 * - Normalize class → struct (C has no classes)
 * - Translate field types via TypeHandler
 * - Handle nested structs with name mangling (Outer__Inner)
 * - Skip polymorphic classes (log warning for now)
 * - Create C RecordDecl with complete definition
 * - Add translated struct to appropriate C TranslationUnit
 *
 * Translation Examples:
 *
 * C++ struct:
 * @code
 * struct Point {
 *     int x;
 *     int y;
 * };
 * @endcode
 *
 * C struct (identical):
 * @code
 * struct Point {
 *     int x;
 *     int y;
 * };
 * @endcode
 *
 * C++ class:
 * @code
 * class Rectangle {
 * public:
 *     int width;
 *     int height;
 * };
 * @endcode
 *
 * C struct (class → struct):
 * @code
 * struct Rectangle {
 *     int width;
 *     int height;
 * };
 * @endcode
 *
 * C++ nested struct:
 * @code
 * struct Outer {
 *     struct Inner {
 *         int value;
 *     };
 *     Inner nested;
 * };
 * @endcode
 *
 * C flattened structs:
 * @code
 * struct Outer__Inner {
 *     int value;
 * };
 * struct Outer {
 *     struct Outer__Inner nested;
 * };
 * @endcode
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper, ...);
 * TypeHandler::registerWith(dispatcher);  // Must register before RecordHandler
 * RecordHandler::registerWith(dispatcher);
 *
 * RecordDecl* cppStruct = ...;
 * dispatcher.dispatch(cppCtx, cCtx, cppStruct);
 * // → Creates C RecordDecl with translated fields
 * @endcode
 */
class RecordHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for RecordDecl
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if declaration is EXACTLY RecordDecl or CXXRecordDecl
     * @param D Declaration to check (must not be null)
     * @return true if D is RecordDecl (struct) or CXXRecordDecl (class)
     *
     * Implementation pattern:
     * 1. Assert D is not null (fails fast on programming errors)
     * 2. Use D->getKind() for exact type matching
     * 3. Accept both Record (plain struct) and CXXRecord (class)
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ struct/class to C struct
     * @param disp Dispatcher for accessing PathMapper and child handlers
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D RecordDecl to process (must not be null)
     *
     * Algorithm:
     * 1. Assert D is not null and is RecordDecl or CXXRecordDecl
     * 2. Cast D to RecordDecl
     * 3. Check declMapper.hasCreated() - skip if already translated
     * 4. Extract struct properties (name, tag type)
     * 5. Detect nesting: Check if getDeclContext() is a RecordDecl
     *    - If nested, compute mangled name (Outer__Inner pattern)
     * 6. Normalize class → struct (TagTypeKind::Struct)
     * 7. Handle forward declaration:
     *    - If not complete definition, create forward C struct with mangled name
     *    - Store mapping and return early
     * 8. Skip polymorphic classes (log warning) - vtables not supported yet
     * 9. Create C RecordDecl with normalized tag and mangled name
     * 10. Store in declMapper EARLY (before translating children)
     * 11. Start definition: RD->startDefinition()
     * 12. Translate nested structs:
     *     - Find nested RecordDecls in decls()
     *     - Skip self-references (nestedRecord == cppRecord)
     *     - Dispatch each to RecordHandler (recursive, auto-mangles names)
     * 13. Translate fields:
     *     - Create FieldDecl for each field
     *     - Dispatch field type via TypeHandler
     *     - Retrieve translated type from TypeMapper
     *     - Create C FieldDecl with translated type
     *     - Add to C RecordDecl
     * 14. Complete definition: RD->completeDefinition()
     * 15. Get target path and C TranslationUnit
     * 16. Add C struct to C TranslationUnit
     * 17. Register node location in PathMapper
     *
     * Phase 1 Limitation: No methods, polymorphism, or inheritance
     * - Methods require separate handler (future phase)
     * - Polymorphism requires vtables (future phase)
     * - Inheritance requires flattening (future phase)
     *
     * @pre D != nullptr && (D->getKind() == Decl::Record || D->getKind() == Decl::CXXRecord) (asserted)
     */
    static void handleRecord(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    /**
     * @brief Translate struct fields by dispatching types to TypeHandler
     * @param cppRecord C++ struct/class declaration
     * @param cRecord C struct declaration (target)
     * @param disp Dispatcher for type translation
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @return Vector of C FieldDecl (created by this handler)
     *
     * Follows Chain of Responsibility pattern: Dispatches each field type
     * to TypeHandler, then creates C FieldDecl with translated type.
     */
    static std::vector<clang::FieldDecl*> translateFields(
        const clang::RecordDecl* cppRecord,
        clang::RecordDecl* cRecord,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Translate nested structs recursively with name mangling
     * @param cppRecord C++ struct/class declaration
     * @param disp Dispatcher for recursive struct translation
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param outerName Outer struct name for mangling (empty for top-level)
     *
     * Nested structs in C++ must be flattened to top-level in C.
     * Name mangling pattern: Outer__Inner (double underscore separator)
     * Example: struct Outer { struct Inner {}; } → struct Outer__Inner {};
     *
     * Recursively dispatches nested RecordDecls to RecordHandler.
     */
    static void translateNestedStructs(
        const clang::RecordDecl* cppRecord,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const std::string& outerName
    );

    // Phase 3: Removed getMangledName() declaration
    // Name mangling now handled by NameMangler::mangleClassName()
    // This provides unified, consistent name mangling across all handlers
};

} // namespace cpptoc
