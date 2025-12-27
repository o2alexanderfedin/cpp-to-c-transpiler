/**
 * @file RecordHandler.h
 * @brief Handler for translating C++ struct/class declarations to C structs
 *
 * Translates C-style struct declarations (without methods) to C structs.
 * Handles basic structs, nested structs, and forward declarations.
 *
 * Scope (Phase 43 + Phase 44 Task 2 + Phase 45):
 * - C-style struct declarations (no methods)
 * - Field declarations
 * - Nested struct declarations
 * - Forward struct declarations
 * - Class keyword normalization to struct
 * - Access specifier stripping (public/private/protected ignored, C has no access control)
 * - Vtable struct generation for polymorphic classes (Phase 45)
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
#include "helpers/VtableTypedefGenerator.h"

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

    /**
     * @brief Generate vtable struct for polymorphic class (Phase 45)
     * @param cxxRecord C++ CXXRecordDecl (must be polymorphic)
     * @param ctx Handler context
     * @return C RecordDecl representing vtable struct, or nullptr if not polymorphic
     *
     * Generates: struct ClassName_vtable {
     *   RetType (*methodName)(struct ClassName *this, ...);
     *   ...
     * };
     *
     * Only generates vtable for polymorphic classes (classes with virtual methods).
     * Uses VtableTypedefGenerator to create strongly-typed function pointer typedefs.
     */
    clang::RecordDecl* generateVtableStruct(
        const clang::CXXRecordDecl* cxxRecord,
        HandlerContext& ctx
    );

    /**
     * @brief Collect all virtual methods from a class (including inherited)
     * @param cxxRecord C++ CXXRecordDecl
     * @return Vector of virtual methods in vtable order
     *
     * Preserves vtable slot order:
     * 1. Destructor (if virtual)
     * 2. Virtual methods from base class(es)
     * 3. New virtual methods introduced in this class
     *
     * Overridden methods preserve their base class slot position.
     */
    std::vector<const clang::CXXMethodDecl*> collectVirtualMethods(
        const clang::CXXRecordDecl* cxxRecord
    );
};

} // namespace cpptoc
