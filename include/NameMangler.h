/**
 * @file NameMangler.h
 * @brief Name mangling for C++ methods to generate unique C function names
 *
 * Story #18: Basic Name Mangling
 * Implements simple name mangling for converting C++ method names to unique
 * C function names. Handles overloading by appending parameter types.
 *
 * Design Principles:
 * - SOLID: Single Responsibility (name generation only)
 * - KISS: Simple ClassName_methodName pattern
 * - DRY: Reusable type name extraction
 *
 * Usage Example:
 * @code
 *   NameMangler mangler(Context);
 *   std::string name = mangler.mangleName(methodDecl);  // "Point_getX"
 * @endcode
 */

#pragma once

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include <string>
#include <set>
#include <vector>

/**
 * @class NameMangler
 * @brief Generates unique C function names from C++ method declarations
 *
 * This class implements basic name mangling for Phase 1 of the transpiler.
 * It handles:
 * - Simple methods: ClassName_methodName
 * - Overloaded methods: ClassName_methodName_int_float
 * - Constructors: ClassName__ctor
 *
 * NOT handled in Phase 1:
 * - Namespace mangling (Phase 2)
 * - Template mangling (Phase 3)
 * - Full Itanium ABI compliance (not needed for readable C)
 */
class NameMangler {
private:
    /// Reference to ASTContext for type analysis
    clang::ASTContext &Ctx;

    /// Track used names to ensure uniqueness
    std::set<std::string> usedNames;

public:
    /**
     * @brief Construct a new NameMangler
     * @param Ctx ASTContext reference for type queries
     */
    explicit NameMangler(clang::ASTContext &Ctx) : Ctx(Ctx) {}

    /**
     * @brief Mangle a C++ method name to a unique C function name
     * @param MD Method declaration
     * @return Mangled name (e.g., "Point_getX" or "Math_add_int_float")
     *
     * Algorithm:
     * 1. Base name: ClassName_methodName
     * 2. If unique, return it
     * 3. If not unique (overload), append parameter types
     * 4. Mark name as used
     */
    std::string mangleName(clang::CXXMethodDecl *MD);

    /**
     * @brief Mangle a C++ constructor to a C init function name
     * @param CD Constructor declaration
     * @return Mangled name (e.g., "Point__ctor")
     *
     * Constructors use __ctor suffix. Overloaded constructors append
     * parameter count.
     */
    std::string mangleConstructor(clang::CXXConstructorDecl *CD);

    /**
     * @brief Mangle a C++ destructor to a C cleanup function name
     * @param DD Destructor declaration
     * @return Mangled name (e.g., "Point__dtor")
     *
     * Destructors use __dtor suffix. Epic #5: RAII + Automatic Destructor Injection
     */
    std::string mangleDestructor(clang::CXXDestructorDecl *DD);

    /**
     * @brief Mangle a C++ class name to C struct name (with namespace support)
     * @param RD Class/record declaration
     * @return Mangled name (e.g., "MyClass" or "ns_MyClass")
     *
     * Story #65: Implements namespace-aware class name mangling
     * Algorithm:
     * 1. Extract namespace hierarchy
     * 2. Build qualified name: ns1_ns2_ClassName
     * 3. Return mangled name
     */
    std::string mangleClassName(clang::CXXRecordDecl *RD);

    /**
     * @brief Mangle a C++ method name with namespace and class support
     * @param MD Method declaration
     * @return Mangled name (e.g., "ns_MyClass_method")
     *
     * Story #65: Full qualified mangling with namespace support
     * Handles: namespace::Class::method -> ns_Class_method
     */
    std::string mangleMethodName(clang::CXXMethodDecl *MD);

    /**
     * @brief Mangle a C++ function name with namespace support
     * @param FD Function declaration
     * @return Mangled name (e.g., "ns_func" or "ns1_ns2_func")
     *
     * Story #65: Namespace-aware function mangling
     * Handles nested namespaces: ns1::ns2::func -> ns1_ns2_func
     */
    std::string mangleFunctionName(clang::FunctionDecl *FD);

private:
    /**
     * @brief Build qualified name from namespace hierarchy
     * @param D Declaration to extract namespaces from
     * @return Vector of namespace names (outermost first)
     *
     * Story #65: Extracts namespace hierarchy for mangling
     * Example: ns1::ns2::Class returns {"ns1", "ns2"}
     */
    std::vector<std::string> extractNamespaceHierarchy(clang::Decl *D);
    /**
     * @brief Get simple type name for mangling
     * @param T QualType to convert
     * @return Simple type name (e.g., "int", "float", "ptr")
     *
     * Simplifies types to readable names for mangling:
     * - int/long/short -> "int"
     * - float/double -> "float"
     * - T* -> "ptr"
     */
    std::string getSimpleTypeName(clang::QualType T);
};
