/**
 * @file StaticMemberTranslator.h
 * @brief Translates C++ static data members to C global variables (Phase 49)
 *
 * Handles the complete translation pipeline for static data members:
 * - Detection of static data members in classes
 * - Generation of extern declarations for headers
 * - Generation of global variable definitions
 * - Linkage between declarations and definitions
 *
 * Design Principles:
 * - SOLID: Single Responsibility (static member translation only)
 * - KISS: Simple global variable generation
 * - DRY: Reuse NameMangler for name generation
 *
 * Usage Example:
 * @code
 *   StaticMemberTranslator translator(ctx);
 *
 *   // Generate extern declaration for header
 *   VarDecl* decl = translator.generateStaticDeclaration(staticMember, ctx);
 *
 *   // Later, generate definition for implementation file
 *   VarDecl* def = translator.generateStaticDefinition(staticMember, ctx);
 * @endcode
 */

#pragma once

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "handlers/HandlerContext.h"
#include <vector>

namespace cpptoc {

/**
 * @class StaticMemberTranslator
 * @brief Translates C++ static data members to C global variables
 *
 * Translation pattern:
 * C++:
 *   class Counter {
 *       static int count;  // Declaration
 *   };
 *   int Counter::count = 0;  // Out-of-class definition
 *
 * C (header):
 *   extern int Counter__count;  // Declaration
 *
 * C (implementation):
 *   int Counter__count = 0;  // Definition
 */
class StaticMemberTranslator {
public:
    /**
     * @brief Detect all static data members in a class
     * @param record C++ class/struct declaration
     * @return Vector of static data member declarations
     *
     * Walks through the class declaration to find all static data members.
     * Uses VarDecl::isStaticDataMember() to identify them.
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
     * @brief Generate C extern declaration for static data member (for header)
     * @param staticMember C++ static data member declaration
     * @param ctx Handler context
     * @return C VarDecl with extern storage class
     *
     * Generates: extern <type> <mangledName>;
     *
     * Example:
     * C++: static int count;
     * C:   extern int Counter__count;
     *
     * The generated VarDecl has:
     * - Translated type
     * - Mangled name (using NameMangler)
     * - SC_Extern storage class
     * - Const qualifier preserved
     */
    static clang::VarDecl* generateStaticDeclaration(
        clang::VarDecl* staticMember,
        HandlerContext& ctx
    );

    /**
     * @brief Generate C global variable definition for static member (for implementation)
     * @param staticMember C++ static data member with definition
     * @param ctx Handler context
     * @return C VarDecl with initializer
     *
     * Generates: <type> <mangledName> = <initializer>;
     *
     * Example:
     * C++: int Counter::count = 0;
     * C:   int Counter__count = 0;
     *
     * The generated VarDecl has:
     * - Translated type
     * - Mangled name (same as declaration)
     * - SC_None storage class (global scope)
     * - Const qualifier preserved
     * - Translated initializer expression
     */
    static clang::VarDecl* generateStaticDefinition(
        clang::VarDecl* staticMember,
        HandlerContext& ctx
    );

    /**
     * @brief Check if a VarDecl is a static data member definition
     * @param varDecl Variable declaration to check
     * @return true if it's a static member definition, false otherwise
     *
     * Detects out-of-class definitions like:
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
     * Given: int Counter::count = 0;
     * Returns: CXXRecordDecl for Counter
     */
    static clang::CXXRecordDecl* getOwningClass(const clang::VarDecl* definition);

private:
    /**
     * @brief Get mangled name for static data member
     * @param record Owning class
     * @param member Static data member
     * @param ctx Handler context
     * @return Mangled name (e.g., "Counter__count")
     *
     * Uses NameMangler to generate consistent names.
     * Pattern: ClassName__memberName
     */
    static std::string getMangledName(
        clang::CXXRecordDecl* record,
        clang::VarDecl* member,
        HandlerContext& ctx
    );
};

} // namespace cpptoc
