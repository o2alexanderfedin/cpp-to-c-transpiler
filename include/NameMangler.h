/**
 * @file NameMangler.h
 * @brief Name mangling for C++ methods to generate unique C function names
 *
 * Story #18: Basic Name Mangling
 * Phase 2: OverloadRegistry Integration
 * Implements deterministic name mangling using global OverloadRegistry for
 * cross-file consistency. Handles overloading by querying registry state.
 *
 * Design Principles:
 * - SOLID: Single Responsibility (name generation only)
 * - KISS: Simple ClassName_methodName pattern
 * - DRY: Reusable type name extraction
 * - Deterministic: Same function always gets same mangled name
 *
 * Usage Example:
 * @code
 *   OverloadRegistry& registry = OverloadRegistry::getInstance();
 *   NameMangler mangler(Context, registry);
 *   std::string name = mangler.mangleName(methodDecl);  // "Point_getX"
 * @endcode
 */

#pragma once

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "OverloadRegistry.h"
#include <string>
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

    /// Reference to global overload registry for deterministic mangling
    cpptoc::OverloadRegistry& registry_;

public:
    /**
     * @brief Construct a new NameMangler
     * @param Ctx ASTContext reference for type queries
     * @param registry Reference to OverloadRegistry for tracking overloads
     *
     * Phase 2: Constructor now requires OverloadRegistry for deterministic
     * name mangling. This ensures the same function gets the same mangled name
     * regardless of file processing order.
     */
    explicit NameMangler(clang::ASTContext &Ctx, cpptoc::OverloadRegistry& registry)
        : Ctx(Ctx), registry_(registry) {}

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
     * @brief Mangle a C++ conversion operator to a C function name
     * @param CD Conversion operator declaration
     * @return Mangled name (e.g., "MyClass_operator_to_int")
     *
     * Phase 53: Conversion operator support
     * Converts operator T() to ClassName_operator_to_T
     * Pattern: ClassName_operator_to_[targetType][_const]
     *
     * Algorithm:
     * 1. Get class name with namespace prefix
     * 2. Extract conversion target type
     * 3. Sanitize target type for C identifier (spaces, *, & become _)
     * 4. Build name: ClassName_operator_to_targetType
     * 5. Append _const if operator is const-qualified
     *
     * Examples:
     * - operator int() -> MyClass_operator_to_int
     * - operator bool() const -> MyClass_operator_to_bool_const
     * - operator std::string() -> MyClass_operator_to_std__string
     */
    std::string mangleConversionOperator(clang::CXXConversionDecl *CD);

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

    /**
     * @brief Mangle a standalone function with overload support
     * @param FD Function declaration
     * @return Mangled name with parameter types if overloaded
     *
     * Phase 8: Standalone function translation
     * Handles overloading by appending parameter types when needed
     * Pattern: functionName_paramType1_paramType2
     * Special cases:
     * - main() is never mangled
     * - extern "C" functions are not mangled
     * - First occurrence of name uses simple name
     * - Subsequent overloads append _paramTypes
     */
    std::string mangleStandaloneFunction(clang::FunctionDecl *FD);

    /**
     * @brief Mangle a C++ static data member to C global variable name
     * @param RD Class/record declaration containing the static member
     * @param VD Static data member declaration
     * @return Mangled name (e.g., "ClassName__memberName")
     *
     * Phase 49: Static data member support
     * Translates C++ static data members to C global variables.
     * Pattern: ClassName__memberName (double underscore)
     *
     * Handles:
     * - Simple classes: Counter::count → Counter__count
     * - Nested classes: Outer::Inner::x → Outer__Inner__x
     * - Namespaced classes: ns::Class::val → ns__Class__val
     * - Namespace + nested: ns::Outer::Inner::x → ns__Outer__Inner__x
     *
     * Name collision avoidance:
     * - Static members use double underscore: Class__member
     * - Methods use single underscore: Class_method
     * - This prevents collisions between static int getValue and int getValue()
     */
    std::string mangleStaticMember(clang::CXXRecordDecl *RD, clang::VarDecl *VD);

private:
    /**
     * @brief Build qualified name from namespace hierarchy
     * @param D Declaration to extract namespaces from
     * @return Vector of namespace names (outermost first)
     *
     * Story #65: Extracts namespace hierarchy for mangling
     * Phase 48: Enhanced with anonymous namespace support
     * Example: ns1::ns2::Class returns {"ns1", "ns2"}
     * Example: namespace { func; } returns {"_anon_<unique_id>"}
     */
    std::vector<std::string> extractNamespaceHierarchy(clang::Decl *D);

    /**
     * @brief Generate unique identifier for anonymous namespace
     * @param ND Anonymous namespace declaration
     * @return Unique identifier based on source location
     *
     * Phase 48: Anonymous namespace support
     * Pattern: _anon_<basename>_<line>
     * Example: _anon_utils_cpp_42 for anonymous namespace at line 42 in utils.cpp
     */
    std::string getAnonymousNamespaceID(clang::NamespaceDecl *ND);
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

    /**
     * @brief Sanitize operator kind to valid C identifier
     * @param Op Operator kind from Clang AST
     * @return Sanitized operator name (e.g., "operator_plus", "operator_indexer")
     *
     * Phase 53: Operator Overloading Support
     * Converts operator symbols to valid C identifiers.
     * Special case: operator[] → "operator_indexer" (user preference)
     */
    std::string sanitizeOperatorName(clang::OverloadedOperatorKind Op);
};
