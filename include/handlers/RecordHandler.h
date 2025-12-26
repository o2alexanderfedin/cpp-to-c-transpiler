/**
 * @file RecordHandler.h
 * @brief Handler for translating C++ struct/class declarations to C structs
 *
 * Translates C-style struct declarations (without methods) to C structs.
 * Handles basic structs, nested structs, and forward declarations.
 *
 * Scope (Phase 43):
 * - C-style struct declarations (no methods)
 * - Field declarations
 * - Nested struct declarations
 * - Forward struct declarations
 * - Class keyword normalization to struct
 *
 * Out of Scope (Future):
 * - Methods (handled by MethodHandler in Phase 44)
 * - Constructors/Destructors (Phase 44)
 * - Inheritance (Phase 45)
 * - Static members (Phase 44+)
 * - Bitfields (defer to later phase)
 */

#pragma once

#include "handlers/ASTHandler.h"

namespace cpptoc {

/**
 * @class RecordHandler
 * @brief Translates C++ struct/class declarations to C structs
 *
 * Example Translation:
 * C++: struct Point { int x; int y; };
 * C:   struct Point { int x; int y; };
 *
 * Nested Struct Strategy:
 * Keep nested structs as-is (C supports nested struct declarations)
 * C++: struct Outer { struct Inner { int x; }; };
 * C:   struct Outer { struct Inner { int x; }; };
 */
class RecordHandler : public ASTHandler {
public:
    /**
     * @brief Check if this handler processes record declarations
     */
    bool canHandle(const clang::Decl* D) const override;

    /**
     * @brief Translate C++ struct/class to C struct
     * @param D C++ RecordDecl
     * @param ctx Handler context
     * @return C RecordDecl
     */
    clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) override;

private:
    /**
     * @brief Translate field declarations
     * @param cppRecord C++ RecordDecl
     * @param cRecord C RecordDecl to add fields to
     * @param ctx Handler context
     */
    void translateFields(
        const clang::RecordDecl* cppRecord,
        clang::RecordDecl* cRecord,
        HandlerContext& ctx
    );

    /**
     * @brief Translate nested record declarations
     * @param cppRecord C++ RecordDecl
     * @param cRecord C RecordDecl to add nested records to
     * @param ctx Handler context
     *
     * Strategy: Keep nested structs in place (C supports this)
     */
    void translateNestedRecords(
        const clang::RecordDecl* cppRecord,
        clang::RecordDecl* cRecord,
        HandlerContext& ctx
    );
};

} // namespace cpptoc
