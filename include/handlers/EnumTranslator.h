/**
 * @file EnumTranslator.h
 * @brief Handler for translating C++ enum declarations to C enums (Phase 47)
 *
 * Translates both scoped and unscoped C++ enums to C-compatible enums.
 * Handles name prefixing for scoped enums and type specifications.
 *
 * Scope (Phase 47):
 * - Unscoped enum declarations (pass-through, no prefixing)
 * - Scoped enum class declarations (enum class → enum, with prefixing)
 * - Enum constant name prefixing (State::Idle → State__Idle)
 * - Enum with explicit values
 * - Enum with underlying type specifications (enum class X : uint8_t)
 * - Typedef generation for type-specified enums
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
 * 3. Enum with type specification (with typedef):
 *    C++: enum class Status : uint8_t { OK = 0, Error = 1 };
 *    C:   typedef enum Status { Status__OK = 0, Status__Error = 1 } Status;
 */

#pragma once

#include "handlers/ASTHandler.h"

namespace cpptoc {

/**
 * @class EnumTranslator
 * @brief Translates C++ enum declarations to C enums
 *
 * Follows the handler chain pattern and Single Responsibility Principle.
 * Only handles enum translation - expression translation is delegated to ExpressionHandler.
 */
class EnumTranslator : public ASTHandler {
public:
    /**
     * @brief Check if this handler processes enum declarations
     */
    bool canHandle(const clang::Decl* D) const override;

    /**
     * @brief Translate C++ enum to C enum
     * @param D C++ EnumDecl
     * @param ctx Handler context
     * @return C EnumDecl
     */
    clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) override;

private:
    /**
     * @brief Translate enum constant with optional prefixing
     * @param ECD C++ EnumConstantDecl
     * @param isScoped Whether parent enum is scoped
     * @param prefix Enum name for prefixing (only used if isScoped)
     * @param parentEnum Parent C EnumDecl
     * @param ctx Handler context
     * @return C EnumConstantDecl
     */
    clang::EnumConstantDecl* translateEnumConstant(
        const clang::EnumConstantDecl* ECD,
        bool isScoped,
        llvm::StringRef prefix,
        clang::EnumDecl* parentEnum,
        HandlerContext& ctx
    );

    /**
     * @brief Extract underlying type from enum declaration
     * @param ED C++ EnumDecl
     * @return Underlying type, or empty QualType if no explicit type
     */
    clang::QualType extractUnderlyingType(const clang::EnumDecl* ED);

    /**
     * @brief Generate typedef for type-specified enum
     * @param C_Enum C EnumDecl
     * @param underlyingType Underlying type
     * @param ctx Handler context
     *
     * Generates: typedef enum Name { ... } Name;
     */
    void generateTypedef(
        const clang::EnumDecl* C_Enum,
        clang::QualType underlyingType,
        HandlerContext& ctx
    );

    /**
     * @brief Generate prefixed name for scoped enum constant
     * @param enumName Enum name
     * @param constantName Constant name
     * @return Prefixed name (EnumName__ConstantName)
     */
    std::string generatePrefixedName(
        llvm::StringRef enumName,
        llvm::StringRef constantName
    );
};

} // namespace cpptoc
