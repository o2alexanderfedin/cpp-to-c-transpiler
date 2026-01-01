/**
 * @file EnumTranslator.h
 * @brief Handler for processing EnumDecl nodes (enum declarations)
 *
 * Registers with CppToCVisitorDispatcher to handle C++ enum declarations.
 * Translates both scoped and unscoped C++ enums to C-compatible enums.
 *
 * Phase 47 Scope: Enum translation
 * - Unscoped enum declarations (pass-through, no prefixing)
 * - Scoped enum class declarations (enum class → enum, with prefixing)
 * - Enum constant name prefixing (State::Idle → State__Idle)
 * - Enum with explicit values
 * - Enum with underlying type specifications (enum class X : uint8_t)
 * - Typedef generation for type-specified enums (handled in CodeGenerator)
 *
 * Translation Patterns:
 * 1. Unscoped enum (direct mapping):
 *    C++: enum Color { Red, Green, Blue };
 *    C:   enum Color { Red, Green, Blue };
 *
 * 2. Scoped enum (with prefixing):
 *    C++: enum class State { Idle, Running };
 *    C:   enum State { State__Idle, State__Running };
 *
 * 3. Enum with type specification (with typedef in CodeGenerator):
 *    C++: enum class Status : uint8_t { OK = 0, Error = 1 };
 *    C:   typedef enum Status { Status__OK = 0, Status__Error = 1 } Status;
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"

namespace cpptoc {

/**
 * @class EnumTranslator
 * @brief Processes EnumDecl and creates C enum declarations
 *
 * Responsibilities:
 * - Match EnumDecl nodes (predicate) - both scoped and unscoped
 * - Translate scoped enums with name prefixing (EnumName__ConstantName)
 * - Translate unscoped enums without prefixing (pass-through)
 * - Handle explicit enum values
 * - Handle underlying type specifications (enum class X : uint8_t)
 * - Create C EnumDecl with complete definition
 * - Add translated enum to appropriate C TranslationUnit
 *
 * Translation Examples:
 *
 * C++ unscoped enum:
 * @code
 * enum Color {
 *     Red,
 *     Green,
 *     Blue
 * };
 * @endcode
 *
 * C enum (identical):
 * @code
 * enum Color {
 *     Red,
 *     Green,
 *     Blue
 * };
 * @endcode
 *
 * C++ scoped enum:
 * @code
 * enum class GameState {
 *     Menu,
 *     Playing,
 *     Paused
 * };
 * @endcode
 *
 * C enum (with prefixing):
 * @code
 * enum GameState {
 *     GameState__Menu,
 *     GameState__Playing,
 *     GameState__Paused
 * };
 * @endcode
 *
 * C++ enum with type:
 * @code
 * enum class Status : uint8_t {
 *     OK = 0,
 *     Error = 1
 * };
 * @endcode
 *
 * C enum (typedef in CodeGenerator):
 * @code
 * typedef enum Status {
 *     Status__OK = 0,
 *     Status__Error = 1
 * } Status;
 * @endcode
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper, ...);
 * EnumTranslator::registerWith(dispatcher);
 *
 * EnumDecl* cppEnum = ...;
 * dispatcher.dispatch(cppCtx, cCtx, cppEnum);
 * // → Creates C EnumDecl with translated constants
 * @endcode
 */
class EnumTranslator {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for EnumDecl
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

private:
    /**
     * @brief Predicate: Check if declaration is EXACTLY EnumDecl
     * @param D Declaration to check (must not be null)
     * @return true if D is EnumDecl
     *
     * Implementation pattern:
     * 1. Assert D is not null (fails fast on programming errors)
     * 2. Use llvm::isa<EnumDecl>(D) for exact type matching
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Translate C++ enum to C enum
     * @param disp Dispatcher for accessing PathMapper and mappers
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D EnumDecl to process (must not be null)
     *
     * Algorithm:
     * 1. Assert D is not null and is EnumDecl
     * 2. Cast D to EnumDecl
     * 3. Check declMapper.hasCreated() - skip if already translated
     * 4. Extract enum properties (name, isScoped, underlying type)
     * 5. Create C EnumDecl (always unscoped - C doesn't support scoped enums)
     * 6. Start definition: ED->startDefinition()
     * 7. Translate enum constants:
     *    - For scoped enums, apply prefixing (EnumName__ConstantName)
     *    - For unscoped enums, use original names
     *    - Preserve explicit values
     *    - Create C EnumConstantDecl for each constant
     *    - Register mapping in declMapper
     *    - Add constant to C EnumDecl
     * 8. Complete definition: ED->completeDefinition()
     * 9. Get target path and C TranslationUnit
     * 10. Add C enum to C TranslationUnit
     * 11. Register node location in PathMapper
     * 12. Register enum mapping in declMapper
     *
     * Note: Typedef generation for type-specified enums is handled
     * by CodeGenerator during code emission, not during AST construction.
     *
     * @pre D != nullptr && D->getKind() == Decl::Enum (asserted)
     */
    static void handleEnum(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    /**
     * @brief Translate enum constant with optional prefixing
     * @param ECD C++ EnumConstantDecl
     * @param isScoped Whether parent enum is scoped
     * @param prefix Enum name for prefixing (only used if isScoped)
     * @param parentEnum Parent C EnumDecl
     * @param cASTContext Target C ASTContext
     * @return C EnumConstantDecl
     *
     * Creates C enum constant with:
     * - Prefixed name for scoped enums (EnumName__ConstantName)
     * - Original name for unscoped enums
     * - Preserved explicit value
     */
    static clang::EnumConstantDecl* translateEnumConstant(
        const clang::EnumConstantDecl* ECD,
        bool isScoped,
        llvm::StringRef prefix,
        clang::EnumDecl* parentEnum,
        clang::ASTContext& cASTContext
    );

    /**
     * @brief Extract underlying type from enum declaration
     * @param ED C++ EnumDecl
     * @return Underlying type, or empty QualType if no explicit type
     *
     * Checks if enum has explicit underlying type (e.g., enum class X : uint8_t)
     * Returns empty QualType for enums without explicit type.
     */
    static clang::QualType extractUnderlyingType(const clang::EnumDecl* ED);

    /**
     * @brief Generate prefixed name for scoped enum constant
     * @param enumName Enum name
     * @param constantName Constant name
     * @return Prefixed name (EnumName__ConstantName)
     *
     * Pattern: EnumName__ConstantName (double underscore separator)
     * Example: GameState::Menu → GameState__Menu
     */
    static std::string generatePrefixedName(
        llvm::StringRef enumName,
        llvm::StringRef constantName
    );
};

} // namespace cpptoc
