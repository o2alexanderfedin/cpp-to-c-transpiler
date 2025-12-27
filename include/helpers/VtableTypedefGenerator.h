/**
 * @file VtableTypedefGenerator.h
 * @brief Generate strongly-typed function pointer typedefs for COM-style vtables
 *
 * This helper class generates typedefs for virtual method function pointers,
 * maintaining type safety and const correctness in the C translation.
 *
 * Design Principles:
 * - SOLID: Single Responsibility (typedef generation only)
 * - KISS: Clear, focused API
 * - DRY: Reusable typedef generation logic
 * - Type Safety: NO void* pointers - strongly typed function pointers
 *
 * Usage Example:
 * @code
 *   VtableTypedefGenerator gen(Context, builder);
 *   TypedefDecl *td = gen.generateTypedef(virtualMethod, "Animal");
 *   // Generates: typedef void (*Animal_speak_fn)(struct Animal *this);
 * @endcode
 *
 * @see Phase 45 Task 1: Vtable Typedef Generator
 */

#ifndef VTABLE_TYPEDEF_GENERATOR_H
#define VTABLE_TYPEDEF_GENERATOR_H

#include "CNodeBuilder.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Type.h"
#include <string>

namespace cpptoc {

/**
 * @class VtableTypedefGenerator
 * @brief Helper class for generating vtable function pointer typedefs
 *
 * Generates strongly-typed function pointer typedefs for virtual methods,
 * ensuring type safety and const correctness in the C translation.
 *
 * Pattern: typedef RetType (*ClassName_methodName_fn)(Params);
 */
class VtableTypedefGenerator {
private:
    /// Reference to C ASTContext for typedef creation
    clang::ASTContext &C_Ctx;

    /// Reference to CNodeBuilder for creating AST nodes
    clang::CNodeBuilder &Builder;

public:
    /**
     * @brief Construct a new VtableTypedefGenerator
     * @param C_Ctx C ASTContext reference for typedef creation
     * @param Builder CNodeBuilder reference for AST node creation
     */
    explicit VtableTypedefGenerator(clang::ASTContext &C_Ctx,
                                   clang::CNodeBuilder &Builder)
        : C_Ctx(C_Ctx), Builder(Builder) {}

    /**
     * @brief Generate typedef for virtual method
     * @param Method C++ virtual method declaration
     * @param ClassName Name of the class (for typedef naming)
     * @return TypedefDecl* for function pointer typedef, or nullptr on error
     *
     * Generates: typedef RetType (*ClassName_methodName_fn)(struct ClassName *this, Params);
     *
     * Example:
     * @code
     *   // Input: virtual void speak();
     *   // Output: typedef void (*Animal_speak_fn)(struct Animal *this);
     * @endcode
     *
     * Handles:
     * - Return types (void, int, pointers, etc.)
     * - Parameters (converted to C types)
     * - Const methods (const this parameter)
     * - Reference parameters (converted to pointers)
     */
    clang::TypedefDecl* generateTypedef(const clang::CXXMethodDecl *Method,
                                        llvm::StringRef ClassName);

    /**
     * @brief Generate typedef for virtual destructor
     * @param Dtor C++ virtual destructor declaration
     * @param ClassName Name of the class (for typedef naming)
     * @return TypedefDecl* for destructor function pointer typedef
     *
     * Generates: typedef void (*ClassName_destructor_fn)(struct ClassName *this);
     *
     * Example:
     * @code
     *   // Input: virtual ~Animal();
     *   // Output: typedef void (*Animal_destructor_fn)(struct Animal *this);
     * @endcode
     */
    clang::TypedefDecl* generateTypedefForDestructor(const clang::CXXDestructorDecl *Dtor,
                                                     llvm::StringRef ClassName);

private:
    /**
     * @brief Build function pointer type for method
     * @param ReturnType Return type of the method
     * @param ParamTypes Parameter types (including this)
     * @return QualType representing function pointer type
     *
     * Creates: RetType (*)(ParamTypes)
     */
    clang::QualType buildFunctionPointerType(clang::QualType ReturnType,
                                             llvm::ArrayRef<clang::QualType> ParamTypes);

    /**
     * @brief Convert C++ type to C type
     * @param CppType C++ type to convert
     * @return QualType representing C equivalent
     *
     * Conversions:
     * - T& → T* (references to pointers)
     * - const T& → const T*
     * - Class types → struct types
     */
    clang::QualType convertTypeToC(clang::QualType CppType);

    /**
     * @brief Build this parameter type
     * @param ClassName Name of the class
     * @param IsConst Whether method is const (const this)
     * @return QualType representing this parameter (struct ClassName *this or const struct ClassName *this)
     */
    clang::QualType buildThisParameterType(llvm::StringRef ClassName, bool IsConst);

    /**
     * @brief Generate typedef name
     * @param ClassName Name of the class
     * @param MethodName Name of the method
     * @return String: ClassName_methodName_fn
     */
    std::string generateTypedefName(llvm::StringRef ClassName, llvm::StringRef MethodName);
};

} // namespace cpptoc

#endif // VTABLE_TYPEDEF_GENERATOR_H
