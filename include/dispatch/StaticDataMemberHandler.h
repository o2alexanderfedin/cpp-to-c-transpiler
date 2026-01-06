/**
 * @file StaticDataMemberHandler.h
 * @brief Handler for translating C++ static data members to C global variables
 *
 * Registers with CppToCVisitorDispatcher to handle VarDecl nodes that are static data members.
 * Translates C++ static data members (class variables) to C global variables with mangled names.
 *
 * Phase 49 Scope: Static data member translation
 * - Detection of static data members in classes
 * - Name mangling (ClassName__memberName pattern)
 * - Generation of extern declarations for headers
 * - Generation of global variable definitions for implementation files
 *
 * Translation Examples:
 *
 * C++ static data member:
 * @code
 * class Counter {
 *     static int count;  // Declaration in class
 * };
 * int Counter::count = 0;  // Out-of-class definition
 * @endcode
 *
 * C global variable (what this handler generates):
 * @code
 * // Header:
 * extern int Counter__count;
 *
 * // Implementation:
 * int Counter__count = 0;
 * @endcode
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include <vector>

namespace cpptoc {

/**
 * @class StaticDataMemberHandler
 * @brief Processes VarDecl (static data members) and creates C global variables
 *
 * Responsibilities:
 * - Match VarDecl nodes that are static data members (predicate)
 * - Translate to C global variables with mangled names
 * - Handle both declarations (extern) and definitions
 * - Generate extern declarations for headers
 * - Generate global variable definitions for implementation files
 * - Use NameMangler for consistent name generation
 *
 * What This Handles vs Other Handlers:
 * - StaticDataMemberHandler: static DATA members (class variables) → C global variables
 * - StaticMethodHandler: static METHODS (functions) → C functions
 * - RecordHandler: instance fields → C struct fields
 * - VariableHandler: local/global variables → C local/global variables
 *
 * Translation Pattern:
 * 1. Detect static data member (VarDecl::isStaticDataMember())
 * 2. Get owning class (CXXRecordDecl)
 * 3. Mangle name (ClassName__memberName)
 * 4. Translate type (future: via TypeHandler dispatch)
 * 5. Create C VarDecl with SC_Extern (declaration) or SC_None (definition)
 * 6. Store mapping in DeclMapper
 * 7. Add to appropriate C TranslationUnit
 */
class StaticDataMemberHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    // ========================================================================
    // Utility Methods (No Dispatcher Needed - Pure Detection/Lookup)
    // ========================================================================

    /**
     * @brief Detect all static data members in a class
     * @param record C++ class/struct declaration
     * @return Vector of static data member declarations
     *
     * Utility method that walks through class declarations to find static data members.
     * Does not require HandlerContext or dispatcher - pure AST navigation.
     *
     * Example:
     * @code
     *   class Stats {
     *       static int count;    // Found
     *       static int total;    // Found
     *       int value;           // NOT found (instance member)
     *   };
     * @endcode
     */
    static std::vector<clang::VarDecl*> detectStaticMembers(
        const clang::CXXRecordDecl* record
    );

    /**
     * @brief Check if a VarDecl is a static data member definition
     * @param varDecl Variable declaration to check
     * @return true if it's a static member definition, false otherwise
     *
     * Utility method that detects out-of-class definitions like:
     * int Counter::count = 0;
     *
     * Criteria:
     * - VarDecl has CXXRecordDecl as DeclContext (class scope)
     * - VarDecl is at file scope (not local variable)
     * - VarDecl is a definition (has initializer or is the definition)
     */
    static bool isStaticMemberDefinition(const clang::VarDecl* varDecl);

    /**
     * @brief Find the class that owns a static member definition
     * @param definition Static member definition (out-of-class)
     * @return CXXRecordDecl of owning class, or nullptr if not found
     *
     * Utility method that extracts the owning class from a static member definition.
     *
     * Given: int Counter::count = 0;
     * Returns: CXXRecordDecl for Counter
     */
    static clang::CXXRecordDecl* getOwningClass(const clang::VarDecl* definition);

private:
    /**
     * @brief Predicate: Check if declaration is a static data member
     * @param D Declaration to check (must not be null)
     * @return true if D is a VarDecl that is a static data member
     *
     * Implementation rules:
     * - Assert D is not null
     * - Check if D is a VarDecl
     * - Check if VarDecl::isStaticDataMember()
     * - Return early on first non-match
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate static data member to C global variable
     * @param disp Dispatcher for accessing mappers and delegating translation
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D VarDecl to process (must be static data member)
     *
     * Translation Steps:
     * 1. Assert D is a VarDecl and is static data member
     * 2. Check if already translated (avoid duplicates)
     * 3. Get owning class (CXXRecordDecl)
     * 4. Mangle name using NameMangler (ClassName__memberName)
     * 5. Get C++ type (TODO: translate via TypeHandler dispatch)
     * 6. Create C VarDecl:
     *    - SC_Extern for declarations (in-class declaration)
     *    - SC_None for definitions (out-of-class definition)
     * 7. Handle initializer (TODO: translate via ExprHandler dispatch)
     * 8. Store mapping in DeclMapper
     * 9. Get target path from PathMapper
     * 10. Add to C TranslationUnit
     * 11. Register location in PathMapper
     *
     * Notes:
     * - Handles both declarations and definitions
     * - Type translation deferred to future phase (uses C++ type for now)
     * - Initializer translation deferred to future phase (copies expression)
     */
    static void handleStaticDataMember(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );
};

} // namespace cpptoc
