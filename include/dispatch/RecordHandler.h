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

    /**
     * @brief Reset static state - clear translated records cache
     *
     * CRITICAL: RecordHandler maintains a static set of translated records (USRs).
     * Must call this between tests to prevent state pollution in test suite runs.
     * This fixes the issue where tests pass individually but fail in full suite.
     */
    static void reset();

    /**
     * @brief Check if a class needs dual layout generation
     * @param cxxRecord C++ class declaration
     * @return true if class needs both ClassName and ClassName__base layouts
     *
     * A class needs dual layout if:
     * 1. It has virtual bases (direct or indirect), OR
     * 2. It is used as a base in a virtual hierarchy
     *
     * Per Itanium C++ ABI, classes with virtual bases require:
     * - ClassName__base: Base-subobject layout (excludes virtual base fields)
     * - ClassName: Complete-object layout (includes virtual base fields)
     *
     * Uses VirtualInheritanceAnalyzer for detection.
     *
     * This method is public so ConstructorHandler can use it to determine
     * if constructor C1/C2 variants are needed.
     */
    static bool needsDualLayout(const clang::CXXRecordDecl* cxxRecord);

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

    /**
     * @brief Generate base-subobject layout (ClassName__base)
     * @param cxxRecord C++ class declaration
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param disp Dispatcher for accessing mappers and handlers
     * @return Created C RecordDecl for base-subobject layout, or nullptr on failure
     *
     * Generates ClassName__base struct per Itanium C++ ABI:
     * 1. Create struct with "__base" suffix
     * 2. Include vbptr if class has virtual bases (using VptrInjector)
     * 3. Include non-virtual base class fields
     * 4. Include own fields
     * 5. EXCLUDE virtual base fields (those belong in complete-object layout)
     *
     * Field ordering follows Itanium ABI:
     * - vbptr (if needed)
     * - Non-virtual base fields
     * - Own fields
     *
     * Used when class is a base-subobject within another class.
     */
    static clang::RecordDecl* generateBaseSubobjectLayout(
        const clang::CXXRecordDecl* cxxRecord,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const CppToCVisitorDispatcher& disp
    );

    /**
     * @brief Generate complete-object layout (ClassName)
     * @param cxxRecord C++ class declaration
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param disp Dispatcher for accessing mappers and handlers
     * @return Created C RecordDecl for complete-object layout, or nullptr on failure
     *
     * Generates ClassName struct per Itanium C++ ABI:
     * 1. Create struct with normal name (no suffix)
     * 2. Include all base class fields (virtual and non-virtual)
     * 3. Include own fields
     * 4. Include virtual base fields AT END
     *
     * Field ordering follows Itanium ABI:
     * - Non-virtual base fields
     * - Own fields
     * - Virtual base fields (at end)
     *
     * Used when class is the most-derived object being constructed.
     */
    static clang::RecordDecl* generateCompleteObjectLayout(
        const clang::CXXRecordDecl* cxxRecord,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const CppToCVisitorDispatcher& disp
    );

    /**
     * @brief Generate implicit C1 (complete-object) constructor for class without explicit constructors
     * @param cxxRecord C++ class declaration
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param disp Dispatcher for accessing mappers and handlers
     *
     * Generates default C1 constructor when class has virtual inheritance but no explicit constructors.
     * C1 constructor is responsible for:
     * 1. Initializing all virtual bases (most-derived class responsibility)
     * 2. Calling C2 (base-subobject) constructors for non-virtual bases
     * 3. Initializing own member fields (if non-POD)
     *
     * Generated function signature: void ClassName__ctor__void_C1(struct ClassName* this)
     */
    static void generateImplicitC1Constructor(
        const clang::CXXRecordDecl* cxxRecord,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const CppToCVisitorDispatcher& disp
    );

    /**
     * @brief Generate implicit C2 (base-subobject) constructor for class without explicit constructors
     * @param cxxRecord C++ class declaration
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     * @param disp Dispatcher for accessing mappers and handlers
     *
     * Generates default C2 constructor when class has virtual inheritance but no explicit constructors.
     * C2 constructor is responsible for:
     * 1. Skipping virtual base initialization (parent's C1 handles it)
     * 2. Calling C2 (base-subobject) constructors for non-virtual bases
     * 3. Initializing own member fields (if non-POD)
     *
     * Generated function signature: void ClassName__ctor__void_C2(struct ClassName__base* this)
     */
    static void generateImplicitC2Constructor(
        const clang::CXXRecordDecl* cxxRecord,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const CppToCVisitorDispatcher& disp
    );

    // Phase 3: Removed getMangledName() declaration
    // Name mangling now handled by NameMangler::mangleClassName()
    // This provides unified, consistent name mangling across all handlers
};

} // namespace cpptoc
