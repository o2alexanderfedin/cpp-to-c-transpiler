/**
 * @file PromiseTranslator.h
 * @brief Story #105: Promise Object Translation
 *
 * Translates C++ promise_type to C structures and functions.
 * The promise object manages the coroutine's state and return value.
 */

#ifndef PROMISE_TRANSLATOR_H
#define PROMISE_TRANSLATOR_H

#include "clang/AST/AST.h"
#include <string>

/**
 * @class PromiseTranslator
 * @brief Translates C++ promise objects to C
 *
 * Translation Pattern:
 *
 * C++ Promise Type:
 * struct generator {
 *     struct promise_type {
 *         int value;
 *         generator get_return_object() { return {}; }
 *         awaiter initial_suspend() { return awaiter(true); }
 *         awaiter final_suspend() noexcept { return awaiter(true); }
 *         awaiter yield_value(int v) { value = v; return awaiter(false); }
 *         void return_void() {}
 *         void unhandled_exception() {}
 *     };
 * };
 *
 * Translated C Structure:
 * struct generator_promise {
 *     int value;
 * };
 *
 * // Helper functions
 * void generator_promise_get_return_object(struct generator_promise* promise);
 * void generator_promise_yield_value(struct generator_promise* promise, int v);
 * void generator_promise_return_void(struct generator_promise* promise);
 *
 * Key Transformations:
 * 1. Extract promise_type from coroutine return type
 * 2. Create C struct with promise data members
 * 3. Translate promise methods to C functions
 * 4. Handle get_return_object, yield_value, return_void, unhandled_exception
 */
class PromiseTranslator {
public:
    /**
     * @brief Construct translator with AST context
     * @param Context Clang AST context
     */
    explicit PromiseTranslator(clang::ASTContext& Context);

    /**
     * @brief Extract promise_type from coroutine return type
     * @param returnType Coroutine return type class
     * @return promise_type declaration or nullptr
     */
    clang::CXXRecordDecl* extractPromiseType(const clang::CXXRecordDecl* returnType);

    /**
     * @brief Generate C struct for promise object
     * @param returnType Coroutine return type class
     * @return C struct definition
     */
    std::string generatePromiseStruct(const clang::CXXRecordDecl* returnType);

    /**
     * @brief Translate get_return_object() method
     * @param returnType Coroutine return type class
     * @return C code for get_return_object
     */
    std::string translateGetReturnObject(const clang::CXXRecordDecl* returnType);

    /**
     * @brief Translate yield_value() method
     * @param returnType Coroutine return type class
     * @return C code for yield_value
     */
    std::string translateYieldValue(const clang::CXXRecordDecl* returnType);

    /**
     * @brief Translate return_void() method
     * @param returnType Coroutine return type class
     * @return C code for return_void
     */
    std::string translateReturnVoid(const clang::CXXRecordDecl* returnType);

    /**
     * @brief Translate unhandled_exception() method
     * @param returnType Coroutine return type class
     * @return C code for unhandled_exception
     */
    std::string translateUnhandledException(const clang::CXXRecordDecl* returnType);

private:
    /**
     * @brief Get promise type name for C struct
     * @param returnType Coroutine return type class
     * @return Promise struct name
     */
    std::string getPromiseStructName(const clang::CXXRecordDecl* returnType);

    /**
     * @brief Translate promise data members to C
     * @param promiseType Promise type declaration
     * @return C struct members
     */
    std::string translatePromiseMembers(const clang::CXXRecordDecl* promiseType);

    clang::ASTContext& Context;
};

#endif // PROMISE_TRANSLATOR_H
