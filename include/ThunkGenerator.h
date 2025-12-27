/**
 * @file ThunkGenerator.h
 * @brief Phase 46, Group 2, Task 5: Thunk Function Generation for Multiple Inheritance
 *
 * Generates this-pointer adjustment thunk functions for non-primary base methods
 * in multiple inheritance scenarios.
 *
 * ## Problem: Non-Primary Base Method Calls
 *
 * When a C++ class inherits from multiple polymorphic bases, vtable pointers
 * for non-primary bases point to different offsets within the derived object.
 * Calling a virtual method through a non-primary base pointer requires adjusting
 * the `this` pointer before calling the real implementation.
 *
 * Example:
 * ```cpp
 * class Base1 { virtual void f1() {} };  // Primary base, offset=0
 * class Base2 { virtual void f2() {} };  // Non-primary base, offset=8
 * class Derived : public Base1, public Base2 {
 *     void f2() override {}  // Real implementation expects Derived* at offset 0
 * };
 * ```
 *
 * When calling through Base2*:
 * - Pointer points to offset 8 in Derived object
 * - Real implementation Derived::f2() expects pointer to offset 0
 * - Need thunk to adjust: `(char*)this - 8`
 *
 * ## Solution: Thunk Functions
 *
 * Generate small "thunk" functions that:
 * 1. Accept this pointer at non-primary base offset
 * 2. Adjust this pointer back to derived class offset (subtract base offset)
 * 3. Call real method implementation with adjusted pointer
 * 4. Forward return value and parameters
 *
 * ## Generated Pattern
 *
 * For Derived : Base1, Base2:
 * ```c
 * // Real implementation
 * void Derived_f2_impl(struct Derived* this) { ... }
 *
 * // Thunk for Base2::f2 (offset=8)
 * void Derived_f2_Base2_thunk(struct Derived* this) {
 *     // Adjust this from Base2* (offset 8) to Derived* (offset 0)
 *     struct Derived* adjusted = (struct Derived*)((char*)this - 8);
 *     Derived_f2_impl(adjusted);
 * }
 *
 * // Vtables
 * struct Derived_Base1_vtable {
 *     void (*f1)(struct Derived*);
 * } = { Derived_f1_impl };  // Primary: direct call
 *
 * struct Derived_Base2_vtable {
 *     void (*f2)(struct Derived*);
 * } = { Derived_f2_Base2_thunk };  // Non-primary: thunk call
 * ```
 *
 * ## Integration
 *
 * - Uses MultipleInheritanceAnalyzer to identify non-primary bases
 * - Uses CNodeBuilder to create C function AST nodes
 * - Generated thunks will be used by VtableInstanceGenerator
 *
 * @see MultipleInheritanceAnalyzer for base identification
 * @see CNodeBuilder for AST node creation
 * @see VtableInstanceGenerator for vtable population (Phase 46, Task 6)
 */

#ifndef THUNK_GENERATOR_H
#define THUNK_GENERATOR_H

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include <vector>
#include <string>

/**
 * @class ThunkGenerator
 * @brief Generates this-pointer adjustment thunk functions for non-primary base methods
 *
 * This class creates small "thunk" functions that adjust the this pointer when
 * calling virtual methods through non-primary base class pointers in multiple
 * inheritance scenarios.
 *
 * ## Thunk Naming Convention
 *
 * Pattern: `ClassName_methodName_BaseName_thunk`
 *
 * Examples:
 * - `Derived_draw_IDrawable_thunk`
 * - `Shape_serialize_ISerializable_thunk`
 * - `Widget_onClick_IClickable_thunk`
 *
 * ## This-Pointer Adjustment
 *
 * The adjustment formula is:
 * ```c
 * adjusted_this = (TargetType*)((char*)this - base_offset)
 * ```
 *
 * Where:
 * - `this`: Pointer at non-primary base offset
 * - `base_offset`: Offset of base within derived class
 * - `adjusted_this`: Pointer at derived class offset
 *
 * ## When Thunks Are NOT Generated
 *
 * 1. Primary base methods (offset == 0, no adjustment needed)
 * 2. Non-virtual methods (no vtable entry)
 * 3. Null inputs (safety)
 *
 * ## Performance
 *
 * - Thunk overhead: 1 pointer adjustment + 1 function call
 * - Typically inlined by optimizing compiler
 * - No runtime overhead in optimized builds
 */
class ThunkGenerator {
public:
    /**
     * @brief Constructor
     * @param ctx Clang AST context for node creation
     * @param astContext Additional AST context (for compatibility)
     *
     * Note: Both parameters may refer to the same ASTContext.
     * This design allows flexibility for different usage patterns.
     */
    explicit ThunkGenerator(clang::ASTContext& ctx, clang::ASTContext& astContext);

    /**
     * @brief Generate a single thunk function for a non-primary base method
     * @param derived The derived class
     * @param method The virtual method to generate thunk for
     * @param nonPrimaryBase The non-primary base class
     * @param baseOffset Offset of base within derived class (in bytes)
     * @return FunctionDecl* for thunk, or nullptr if thunk not needed
     *
     * Returns nullptr if:
     * - Any parameter is null
     * - baseOffset is 0 (primary base, no adjustment needed)
     * - method is not virtual (no vtable entry)
     *
     * Generated thunk:
     * 1. Has same signature as original method
     * 2. Adjusts this pointer: `(char*)this - baseOffset`
     * 3. Calls real implementation with adjusted pointer
     * 4. Forwards all parameters
     * 5. Forwards return value
     *
     * Example:
     * ```c
     * // For: void Derived::method(int x)
     * // Base offset: 8 bytes
     * void Derived_method_Base_thunk(struct Derived* this, int x) {
     *     struct Derived* adjusted = (struct Derived*)((char*)this - 8);
     *     return Derived_method_impl(adjusted, x);
     * }
     * ```
     */
    clang::FunctionDecl* generateThunk(
        const clang::CXXRecordDecl* derived,
        const clang::CXXMethodDecl* method,
        const clang::CXXRecordDecl* nonPrimaryBase,
        uint64_t baseOffset
    );

    /**
     * @brief Generate all thunks for a derived class
     * @param derived The derived class with multiple inheritance
     * @return Vector of FunctionDecl* for all generated thunks
     *
     * For each non-primary polymorphic base:
     * 1. Identify virtual methods that need thunks
     * 2. Calculate base offset
     * 3. Generate thunk function
     *
     * Returns empty vector if:
     * - derived is null
     * - derived has no non-primary bases
     * - derived has no virtual methods
     *
     * Algorithm:
     * ```
     * for each non-primary base:
     *     for each virtual method in base:
     *         if method is overridden in derived:
     *             generate thunk for method
     * ```
     */
    std::vector<clang::FunctionDecl*> generateAllThunks(
        const clang::CXXRecordDecl* derived
    );

    /**
     * @brief Get thunk name for a method
     * @param derived The derived class
     * @param method The virtual method
     * @param base The base class
     * @return Thunk name following pattern: ClassName_methodName_BaseName_thunk
     *
     * Returns empty string if any parameter is null.
     *
     * Examples:
     * - Derived::method() via Base2 -> "Derived_method_Base2_thunk"
     * - Shape::draw() via IDrawable -> "Shape_draw_IDrawable_thunk"
     * - Widget::onClick() via IClickable -> "Widget_onClick_IClickable_thunk"
     */
    std::string getThunkName(
        const clang::CXXRecordDecl* derived,
        const clang::CXXMethodDecl* method,
        const clang::CXXRecordDecl* base
    );

private:
    clang::ASTContext& Ctx;
    clang::ASTContext& ASTCtx;

    /**
     * @brief Get real implementation function name for a method
     * @param derived The derived class
     * @param method The method
     * @return Function name: ClassName_methodName_impl
     */
    std::string getRealImplName(
        const clang::CXXRecordDecl* derived,
        const clang::CXXMethodDecl* method
    );

    /**
     * @brief Create function parameters for thunk
     * @param method Original method
     * @param derivedTypeName Name of derived class for 'this' parameter type
     * @return Vector of ParmVarDecl for thunk signature
     *
     * First parameter is always: struct DerivedClass* this
     * Remaining parameters match original method signature
     */
    std::vector<clang::ParmVarDecl*> createThunkParams(
        const clang::CXXMethodDecl* method,
        const std::string& derivedTypeName
    );

    /**
     * @brief Create thunk body that adjusts this and calls real implementation
     * @param derived The derived class
     * @param method The method
     * @param baseOffset Offset to subtract from this pointer
     * @param thunkParams Parameters of thunk function
     * @return CompoundStmt* representing thunk body
     *
     * Generates:
     * ```c
     * {
     *     struct Derived* adjusted = (struct Derived*)((char*)this - offset);
     *     return RealImpl(adjusted, param1, param2, ...);
     * }
     * ```
     */
    clang::CompoundStmt* createThunkBody(
        const clang::CXXRecordDecl* derived,
        const clang::CXXMethodDecl* method,
        uint64_t baseOffset,
        const std::vector<clang::ParmVarDecl*>& thunkParams
    );
};

#endif // THUNK_GENERATOR_H
