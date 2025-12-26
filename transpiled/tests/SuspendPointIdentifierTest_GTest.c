// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/SuspendPointIdentifierTest_GTest.cpp
// Implementation file

#include "SuspendPointIdentifierTest_GTest.h"

static void SuspendPoint__ctor_default(struct SuspendPoint * this) {
	this->kind = 0;
	this->line = 0;
	this->column = 0;
	this->stateId = 0;
	this->stmt = 0;
}

static void SuspendPoint__ctor_copy(struct SuspendPoint * this, const struct SuspendPoint * other) {
	this->kind = other->kind;
	this->line = other->line;
	this->column = other->column;
	this->stateId = other->stateId;
	this->stmt = other->stmt;
}

static void SuspendPointIdentifier__ctor_default(struct SuspendPointIdentifier * this) {
	this->Context = 0;
}

static void SuspendPointIdentifier__ctor_copy(struct SuspendPointIdentifier * this, const struct SuspendPointIdentifier * other) {
	this->Context = other->Context;
}

static void SuspendPointIdentifierTestFixture__ctor_default(struct SuspendPointIdentifierTestFixture * this) {
}

static void SuspendPointIdentifierTestFixture__ctor_copy(struct SuspendPointIdentifierTestFixture * this, const struct SuspendPointIdentifierTestFixture * other) {
}

int SuspendPointIdentifierTestFixture_buildAST(struct SuspendPointIdentifierTestFixture * this, const char * code) {
}

int * SuspendPointIdentifierTestFixture_findFunction(struct SuspendPointIdentifierTestFixture * this, int * TU, const int * name) {
	return nullptr;
;
}

int TEST_F(struct SuspendPointIdentifierTestFixture, int) {
	const char *code = "\n        struct task;\n        namespace std {\n            template<typename Promise = void>\n            struct coroutine_handle {\n                static coroutine_handle from_address(void* addr) noexcept { return {}; }\n            };\n            template<typename T, typename... Args>\n            struct coroutine_traits {\n                using promise_type = typename T::promise_type;\n            };\n        }\n        struct task {\n            struct promise_type {\n                struct awaiter {\n                    bool await_ready() noexcept { return false; }\n                    template<typename P> void await_suspend(std::coroutine_handle<P>) noexcept {}\n                    void await_resume() noexcept {}\n                };\n                task get_return_object() { return {}; }\n                awaiter initial_suspend() { return {}; }\n                awaiter final_suspend() noexcept { return {}; }\n                void return_void() {}\n                void unhandled_exception() {}\n            };\n        };\n        task async_func() {\n            co_await task::promise_type::awaiter{};\n            co_await task::promise_type::awaiter{};\n        }\n    ";

	auto AST;

	struct SuspendPointIdentifier identifier;

	auto * TU;
	auto *func;

	auto suspendPoints;

}

int TEST_F_SuspendPointIdentifierTestFixture_int(struct SuspendPointIdentifierTestFixture, int) {
	const char *code = "\n        struct generator;\n        namespace std {\n            template<typename Promise = void>\n            struct coroutine_handle {\n                static coroutine_handle from_address(void* addr) noexcept { return {}; }\n            };\n            template<typename T, typename... Args>\n            struct coroutine_traits {\n                using promise_type = typename T::promise_type;\n            };\n        }\n        struct generator {\n            struct promise_type {\n                struct awaiter {\n                    bool await_ready_val;\n                    awaiter(bool ready) : await_ready_val(ready) {}\n                    bool await_ready() noexcept { return await_ready_val; }\n                    template<typename P> void await_suspend(std::coroutine_handle<P>) noexcept {}\n                    void await_resume() noexcept {}\n                };\n                int value;\n                generator get_return_object() { return {}; }\n                awaiter initial_suspend() { return awaiter(true); }\n                awaiter final_suspend() noexcept { return awaiter(true); }\n                awaiter yield_value(int v) { value = v; return awaiter(false); }\n                void return_void() {}\n                void unhandled_exception() {}\n            };\n        };\n        generator produce_values() {\n            co_yield 1;\n            co_yield 2;\n            co_yield 3;\n        }\n    ";

	auto AST;

	struct SuspendPointIdentifier identifier;

	auto * TU;
	auto *func;

	auto suspendPoints;

}

int TEST_F_SuspendPointIdentifierTestFixture_int_1(struct SuspendPointIdentifierTestFixture, int) {
	const char *code = "\n        struct task;\n        namespace std {\n            template<typename Promise = void>\n            struct coroutine_handle {\n                static coroutine_handle from_address(void* addr) noexcept { return {}; }\n            };\n            template<typename T, typename... Args>\n            struct coroutine_traits {\n                using promise_type = typename T::promise_type;\n            };\n        }\n        struct task {\n            struct promise_type {\n                struct awaiter {\n                    bool await_ready() noexcept { return false; }\n                    template<typename P> void await_suspend(std::coroutine_handle<P>) noexcept {}\n                    void await_resume() noexcept {}\n                };\n                task get_return_object() { return {}; }\n                awaiter initial_suspend() { return {}; }\n                awaiter final_suspend() noexcept { return {}; }\n                void return_void() {}\n                void unhandled_exception() {}\n            };\n        };\n        task simple_coro() {\n            co_return;\n        }\n    ";

	auto AST;

	struct SuspendPointIdentifier identifier;

	auto * TU;
	auto *func;

	auto suspendPoints;

}

int TEST_F_SuspendPointIdentifierTestFixture_int_2(struct SuspendPointIdentifierTestFixture, int) {
	const char *code = "\n        struct generator;\n        namespace std {\n            template<typename Promise = void>\n            struct coroutine_handle {\n                static coroutine_handle from_address(void* addr) noexcept { return {}; }\n            };\n            template<typename T, typename... Args>\n            struct coroutine_traits {\n                using promise_type = typename T::promise_type;\n            };\n        }\n        struct generator {\n            struct promise_type {\n                struct awaiter {\n                    bool await_ready_val;\n                    awaiter(bool ready) : await_ready_val(ready) {}\n                    bool await_ready() noexcept { return await_ready_val; }\n                    template<typename P> void await_suspend(std::coroutine_handle<P>) noexcept {}\n                    void await_resume() noexcept {}\n                };\n                int value;\n                generator get_return_object() { return {}; }\n                awaiter initial_suspend() { return awaiter(true); }\n                awaiter final_suspend() noexcept { return awaiter(true); }\n                awaiter yield_value(int v) { value = v; return awaiter(false); }\n                void return_void() {}\n                void unhandled_exception() {}\n            };\n        };\n        generator count() {\n            co_yield 1;\n            co_yield 2;\n        }\n    ";

	auto AST;

	struct SuspendPointIdentifier identifier;

	auto * TU;
	auto *func;

	auto suspendPoints;

}

int TEST_F_SuspendPointIdentifierTestFixture_int_3(struct SuspendPointIdentifierTestFixture, int) {
	const char *code = "\n        struct generator;\n        namespace std {\n            template<typename Promise = void>\n            struct coroutine_handle {\n                static coroutine_handle from_address(void* addr) noexcept { return {}; }\n            };\n            template<typename T, typename... Args>\n            struct coroutine_traits {\n                using promise_type = typename T::promise_type;\n            };\n        }\n        struct generator {\n            struct promise_type {\n                struct awaiter {\n                    bool await_ready_val;\n                    awaiter(bool ready) : await_ready_val(ready) {}\n                    bool await_ready() noexcept { return await_ready_val; }\n                    template<typename P> void await_suspend(std::coroutine_handle<P>) noexcept {}\n                    void await_resume() noexcept {}\n                };\n                int value;\n                generator get_return_object() { return {}; }\n                awaiter initial_suspend() { return awaiter(true); }\n                awaiter final_suspend() noexcept { return awaiter(true); }\n                awaiter yield_value(int v) { value = v; return awaiter(false); }\n                void return_void() {}\n                void unhandled_exception() {}\n            };\n        };\n        generator mixed() {\n            co_yield 42;\n            co_return;\n        }\n    ";

	auto AST;

	struct SuspendPointIdentifier identifier;

	auto * TU;
	auto *func;

	auto suspendPoints;

	bool hasYield = false;

	bool hasReturn = false;

}

int TEST_F_SuspendPointIdentifierTestFixture_int_4(struct SuspendPointIdentifierTestFixture, int) {
	const char *code = "\n        struct generator;\n        namespace std {\n            template<typename Promise = void>\n            struct coroutine_handle {\n                static coroutine_handle from_address(void* addr) noexcept { return {}; }\n            };\n            template<typename T, typename... Args>\n            struct coroutine_traits {\n                using promise_type = typename T::promise_type;\n            };\n        }\n        struct generator {\n            struct promise_type {\n                struct awaiter {\n                    bool await_ready_val;\n                    awaiter(bool ready) : await_ready_val(ready) {}\n                    bool await_ready() noexcept { return await_ready_val; }\n                    template<typename P> void await_suspend(std::coroutine_handle<P>) noexcept {}\n                    void await_resume() noexcept {}\n                };\n                int value;\n                generator get_return_object() { return {}; }\n                awaiter initial_suspend() { return awaiter(true); }\n                awaiter final_suspend() noexcept { return awaiter(true); }\n                awaiter yield_value(int v) { value = v; return awaiter(false); }\n                void return_void() {}\n                void unhandled_exception() {}\n            };\n        };\n        generator gen() {\n            co_yield 1;\n            co_yield 2;\n        }\n    ";

	auto AST;

	struct SuspendPointIdentifier identifier;

	auto * TU;
	auto *func;

	int stateLabels;

}

int TEST_F_SuspendPointIdentifierTestFixture_int_5(struct SuspendPointIdentifierTestFixture, int) {
	const char *code = "\n        struct generator;\n        namespace std {\n            template<typename Promise = void>\n            struct coroutine_handle {\n                static coroutine_handle from_address(void* addr) noexcept { return {}; }\n            };\n            template<typename T, typename... Args>\n            struct coroutine_traits {\n                using promise_type = typename T::promise_type;\n            };\n        }\n        struct generator {\n            struct promise_type {\n                struct awaiter {\n                    bool await_ready_val;\n                    awaiter(bool ready) : await_ready_val(ready) {}\n                    bool await_ready() noexcept { return await_ready_val; }\n                    template<typename P> void await_suspend(std::coroutine_handle<P>) noexcept {}\n                    void await_resume() noexcept {}\n                };\n                int value;\n                generator get_return_object() { return {}; }\n                awaiter initial_suspend() { return awaiter(true); }\n                awaiter final_suspend() noexcept { return awaiter(true); }\n                awaiter yield_value(int v) { value = v; return awaiter(false); }\n                void return_void() {}\n                void unhandled_exception() {}\n            };\n        };\n        generator sequential() {\n            co_yield 1;\n            co_yield 2;\n            co_yield 3;\n        }\n    ";

	auto AST;

	struct SuspendPointIdentifier identifier;

	auto * TU;
	auto *func;

	auto suspendPoints;

}

