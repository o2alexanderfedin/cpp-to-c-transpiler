/**
 * @file VptrInjector.h
 * @brief Story #169: Vptr Field Injection in Class Layout
 *
 * Injects vtable pointer (vptr) as the first field in polymorphic classes.
 * The vptr field enables virtual dispatch and must be at offset 0 for
 * correct C++ ABI compatibility and derived-to-base casts.
 */

#ifndef VPTR_INJECTOR_H
#define VPTR_INJECTOR_H

#include "clang/AST/AST.h"
#include "VirtualMethodAnalyzer.h"
#include <vector>

/**
 * @class VptrInjector
 * @brief Injects vptr field in polymorphic classes
 *
 * Responsibilities:
 * - Detect polymorphic classes (via VirtualMethodAnalyzer)
 * - Inject vptr as first field (offset 0)
 * - Generate correct vptr type (const struct {ClassName}_vtable*)
 * - Maintain ABI compatibility with C++ memory layout
 *
 * Memory Layout:
 * Offset 0:  vptr (8 bytes on 64-bit)
 * Offset 8:  first member field
 * Offset 16: second member field
 * ...
 *
 * Example:
 * C++: class Shape { virtual void draw(); double x; };
 * C:   struct Shape { const struct Shape_vtable *vptr; double x; };
 */
class VptrInjector {
public:
    /**
     * @brief Construct injector with AST context and virtual method analyzer
     * @param Context Clang AST context
     * @param Analyzer Virtual method analyzer for polymorphism detection
     */
    VptrInjector(clang::ASTContext& Context, VirtualMethodAnalyzer& Analyzer);

    /**
     * @brief Inject vptr field for a polymorphic class
     * @param Record C++ class to inject vptr into
     * @param fields Field list to prepend vptr to (modified in-place)
     * @return true if vptr was injected, false if class is not polymorphic
     *
     * Side effects:
     * - If Record is polymorphic, prepends vptr field to fields vector
     * - If Record is not polymorphic, fields vector is unchanged
     */
    bool injectVptrField(const clang::CXXRecordDecl* Record,
                         std::vector<clang::FieldDecl*>& fields);

    /**
     * @brief Get vptr field name (always "vptr")
     * @return String reference to vptr field name
     */
    static const std::string& getVptrFieldName();

    /**
     * @brief Generate vtable struct type name for a class
     * @param ClassName Name of the C++ class
     * @return Vtable struct name (e.g., "Shape_vtable")
     */
    static std::string getVtableTypeName(const std::string& ClassName);

private:
    /**
     * @brief Create vptr field declaration
     * @param Record C++ class that owns the vptr
     * @return FieldDecl for vptr field
     */
    clang::FieldDecl* createVptrField(const clang::CXXRecordDecl* Record);

    /**
     * @brief Build vptr type: const struct {ClassName}_vtable*
     * @param Record C++ class to build vptr type for
     * @return QualType for vptr (const pointer to vtable struct)
     */
    clang::QualType buildVptrType(const clang::CXXRecordDecl* Record);

    clang::ASTContext& Context;
    VirtualMethodAnalyzer& Analyzer;
};

#endif // VPTR_INJECTOR_H
