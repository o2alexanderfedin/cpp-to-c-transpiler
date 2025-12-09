/**
 * @file VirtualCallTranslator.h
 * @brief Story #172: Virtual Call Translation to Vtable Dispatch
 *
 * Translates C++ virtual method calls to vtable dispatch calls in C.
 * Transforms: obj->method(args) to obj->vptr->method(obj, args)
 */

#ifndef VIRTUAL_CALL_TRANSLATOR_H
#define VIRTUAL_CALL_TRANSLATOR_H

#include "clang/AST/AST.h"
#include "VirtualMethodAnalyzer.h"
#include <string>

/**
 * @class VirtualCallTranslator
 * @brief Translates virtual method calls to vtable dispatch
 *
 * Responsibilities:
 * - Detect virtual method calls (CXXMemberCallExpr)
 * - Transform to vtable lookup: obj->vptr->method
 * - Pass 'this' pointer as first argument
 * - Forward remaining arguments
 *
 * Example:
 * C++: shape->draw()
 * C:   shape->vptr->draw(shape)
 *
 * C++: shape->setColor(red, 255)
 * C:   shape->vptr->setColor(shape, red, 255)
 */
class VirtualCallTranslator {
public:
    /**
     * @brief Construct translator with AST context and analyzer
     * @param Context Clang AST context
     * @param Analyzer Virtual method analyzer
     */
    VirtualCallTranslator(clang::ASTContext& Context, VirtualMethodAnalyzer& Analyzer);

    /**
     * @brief Check if a method call is virtual
     * @param CallExpr Method call expression
     * @return true if call is to a virtual method
     */
    bool isVirtualCall(const clang::CXXMemberCallExpr* CallExpr) const;

    /**
     * @brief Get method name for vtable lookup
     * @param Method Method being called
     * @return Method name for vtable (e.g., "draw", "destructor")
     */
    std::string getVtableMethodName(const clang::CXXMethodDecl* Method) const;

private:
    clang::ASTContext& Context;
    VirtualMethodAnalyzer& Analyzer;
};

#endif // VIRTUAL_CALL_TRANSLATOR_H
