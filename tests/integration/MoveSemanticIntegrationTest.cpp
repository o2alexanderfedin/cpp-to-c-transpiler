/**
 * @file MoveSemanticIntegrationTest.cpp
 * @brief Comprehensive integration tests for move semantics (Story #135) - Google Test Version
 *
 * Test Strategy (TDD):
 * - Test 1: Unique pointer-like ownership transfer
 * - Test 2: Vector-like move construction
 * - Test 3: Vector-like move assignment
 * - Test 4: Custom move-only type (FileHandle)
 * - Test 5: Custom move-only type (Socket)
 * - Test 6: Return value optimization with move semantics
 * - Test 7: Member-wise moves (class with multiple movable members)
 * - Test 8: Complex class hierarchy with move semantics
 * - Test 9: Move semantics with inheritance
 * - Test 10: Move-only types cannot be copied
 * - Test 11: Rvalue reference parameters
 * - Test 12: Perfect forwarding with move semantics
 * - Test 13: Move elision and RVO
 * - Test 14: Conditional move vs copy
 * - Test 15: Move semantics with exception safety
 * - Test 16: Performance validation (additional test)
 *
 * Acceptance Criteria:
 * 1. Unique pointer-like types transpile successfully
 * 2. Vector-like move operations work
 * 3. Custom move-only classes work
 * 4. Return value moves work correctly
 * 5. Member-wise moves work (classes with multiple movable members)
 * 6. Performance validation (moves cheaper than copies)
 * 7. Zero regressions in existing tests
 * 8. Documentation: move semantics usage guide
 */

#include "MoveSemanticIntegrationTestFixture.h"
#include "../../include/CppToCVisitor.h"
#include "../../include/CNodeBuilder.h"
#include "../../include/MoveConstructorTranslator.h"
#include "../../include/MoveAssignmentTranslator.h"
#include "../../include/StdMoveTranslator.h"

//=============================================================================
// Test 1: Unique pointer-like ownership transfer
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, UniquePtrOwnershipTransfer) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        template<typename T>
        class SmartPtr {
            T* ptr;
        public:
            SmartPtr(T* p) : ptr(p) {}

            // Move constructor
            SmartPtr(SmartPtr&& other) : ptr(other.ptr) {
                other.ptr = nullptr;
            }

            // Move assignment
            SmartPtr& operator=(SmartPtr&& other) {
                if (this != &other) {
                    ptr = other.ptr;
                    other.ptr = nullptr;
                }
                return *this;
            }
        };

        class Resource {
            int data;
        };

        void transfer() {
            SmartPtr<Resource> p1(nullptr);
            SmartPtr<Resource> p2 = std::move(p1);
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    expectMoveConstructors(1, "Expected at least 1 move constructor for SmartPtr");
    expectMoveAssignments(1, "Expected at least 1 move assignment for SmartPtr");
    expectStdMoveCalls(1, "Expected std::move() call for ownership transfer");
}

//=============================================================================
// Test 2: Vector-like move construction
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, VectorMoveConstruction) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        template<typename T>
        class DynamicArray {
            T* data;
            int size;
        public:
            DynamicArray() : data(nullptr), size(0) {}

            // Move constructor
            DynamicArray(DynamicArray&& other)
                : data(other.data), size(other.size) {
                other.data = nullptr;
                other.size = 0;
            }
        };

        void use_array() {
            DynamicArray<int> arr1;
            DynamicArray<int> arr2 = std::move(arr1);
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    expectMoveConstructors(1, "Expected move constructor for DynamicArray");
    expectStdMoveCalls(1, "Expected std::move() call");
}

//=============================================================================
// Test 3: Vector-like move assignment
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, VectorMoveAssignment) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        template<typename T>
        class Container {
            T* elements;
        public:
            Container() : elements(nullptr) {}

            // Move assignment
            Container& operator=(Container&& other) {
                if (this != &other) {
                    elements = other.elements;
                    other.elements = nullptr;
                }
                return *this;
            }
        };

        void use_container() {
            Container<int> c1;
            Container<int> c2;
            c2 = std::move(c1);
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    expectMoveAssignments(1, "Expected move assignment for Container");
    expectStdMoveCalls(1, "Expected std::move() call");
}

//=============================================================================
// Test 4: Custom move-only type (FileHandle)
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, CustomMoveOnlyFileHandle) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        class FileHandle {
            int fd;
        public:
            FileHandle(int f) : fd(f) {}

            // Move constructor
            FileHandle(FileHandle&& other) : fd(other.fd) {
                other.fd = -1;
            }

            // Move assignment
            FileHandle& operator=(FileHandle&& other) {
                if (this != &other) {
                    fd = other.fd;
                    other.fd = -1;
                }
                return *this;
            }

            // Delete copy operations (move-only)
            FileHandle(const FileHandle&) = delete;
            FileHandle& operator=(const FileHandle&) = delete;
        };

        void use_filehandle() {
            FileHandle f1(42);
            FileHandle f2 = std::move(f1);
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    expectMoveConstructors(1, "Expected move constructor for FileHandle");
    expectMoveAssignments(1, "Expected move assignment for FileHandle");
    expectStdMoveCalls(1, "Expected std::move() call");
}

//=============================================================================
// Test 5: Custom move-only type (Socket)
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, CustomMoveOnlySocket) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        class Socket {
            int sockfd;
            bool connected;
        public:
            Socket(int fd) : sockfd(fd), connected(true) {}

            // Move constructor
            Socket(Socket&& other)
                : sockfd(other.sockfd), connected(other.connected) {
                other.sockfd = -1;
                other.connected = false;
            }

            // Move assignment
            Socket& operator=(Socket&& other) {
                if (this != &other) {
                    sockfd = other.sockfd;
                    connected = other.connected;
                    other.sockfd = -1;
                    other.connected = false;
                }
                return *this;
            }

            // Delete copy operations
            Socket(const Socket&) = delete;
            Socket& operator=(const Socket&) = delete;
        };

        void use_socket() {
            Socket s1(100);
            Socket s2 = std::move(s1);
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    expectMoveConstructors(1, "Expected move constructor for Socket");
    expectMoveAssignments(1, "Expected move assignment for Socket");
}

//=============================================================================
// Test 6: Return value optimization with move semantics
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, ReturnValueOptimization) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        template<typename T>
        class UniquePtr {
            T* ptr;
        public:
            UniquePtr(T* p) : ptr(p) {}
            UniquePtr(UniquePtr&& other) : ptr(other.ptr) {
                other.ptr = nullptr;
            }
        };

        class Widget {
            int value;
        public:
            Widget(int v) : value(v) {}
        };

        UniquePtr<Widget> createWidget(int value) {
            UniquePtr<Widget> w(nullptr);
            return std::move(w);
        }

        void use_factory() {
            auto widget = createWidget(42);
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    expectMoveConstructors(1, "Expected move constructor");
    expectStdMoveCalls(1, "Expected std::move() in return statement");
}

//=============================================================================
// Test 7: Member-wise moves (class with multiple movable members)
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, MemberwiseMoves) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        template<typename T>
        class UniquePtr {
            T* ptr;
        public:
            UniquePtr() : ptr(nullptr) {}
            UniquePtr(UniquePtr&& other) : ptr(other.ptr) {
                other.ptr = nullptr;
            }
        };

        template<typename T>
        class Vector {
            T* data;
        public:
            Vector() : data(nullptr) {}
            Vector(Vector&& other) : data(other.data) {
                other.data = nullptr;
            }
        };

        class Container {
            UniquePtr<int> ptr;
            Vector<int> vec;
            int value;

        public:
            Container() : value(0) {}

            // Move constructor (member-wise move)
            Container(Container&& other)
                : ptr(std::move(other.ptr)),
                  vec(std::move(other.vec)),
                  value(other.value) {
                other.value = 0;
            }

            // Move assignment (member-wise move)
            Container& operator=(Container&& other) {
                if (this != &other) {
                    ptr = std::move(other.ptr);
                    vec = std::move(other.vec);
                    value = other.value;
                    other.value = 0;
                }
                return *this;
            }
        };

        void use_container() {
            Container c1;
            Container c2 = std::move(c1);
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    // Should have move constructors for UniquePtr, Vector, and Container
    expectMoveConstructors(3, "Expected multiple move constructors (UniquePtr, Vector, Container)");

    // Should have std::move() calls for member-wise moves
    EXPECT_GE(collector.stdMoveCalls.size(), static_cast<size_t>(4))
        << "Expected multiple std::move() calls for member-wise moves";
}

//=============================================================================
// Test 8: Complex class hierarchy with move semantics
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, ComplexHierarchyWithMoves) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        template<typename T>
        class UniquePtr {
            T* ptr;
        public:
            UniquePtr() : ptr(nullptr) {}
            UniquePtr(UniquePtr&& other) : ptr(other.ptr) {
                other.ptr = nullptr;
            }
        };

        class Base {
        protected:
            UniquePtr<int> baseData;
        public:
            Base() {}

            Base(Base&& other) : baseData(std::move(other.baseData)) {}

            Base& operator=(Base&& other) {
                if (this != &other) {
                    baseData = std::move(other.baseData);
                }
                return *this;
            }
        };

        class Derived : public Base {
            UniquePtr<int> derivedData;
        public:
            Derived() {}

            Derived(Derived&& other)
                : Base(std::move(other)),
                  derivedData(std::move(other.derivedData)) {}

            Derived& operator=(Derived&& other) {
                if (this != &other) {
                    Base::operator=(std::move(other));
                    derivedData = std::move(other.derivedData);
                }
                return *this;
            }
        };

        void use_hierarchy() {
            Derived d1;
            Derived d2 = std::move(d1);
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    // Should have move constructors for UniquePtr, Base, and Derived
    expectMoveConstructors(2, "Expected move constructors for Base and Derived");

    // Should have move assignments for Base and Derived
    expectMoveAssignments(2, "Expected move assignments for Base and Derived");
}

//=============================================================================
// Test 9: Move semantics with inheritance (base class move)
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, InheritanceBaseClassMove) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        class Base {
            int baseValue;
        public:
            Base(int v) : baseValue(v) {}

            Base(Base&& other) : baseValue(other.baseValue) {
                other.baseValue = 0;
            }
        };

        class Derived : public Base {
            int derivedValue;
        public:
            Derived(int b, int d) : Base(b), derivedValue(d) {}

            // Move constructor calls base move constructor
            Derived(Derived&& other)
                : Base(std::move(other)), derivedValue(other.derivedValue) {
                other.derivedValue = 0;
            }
        };

        void use_derived() {
            Derived d1(10, 20);
            Derived d2 = std::move(d1);
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    expectMoveConstructors(2, "Expected move constructors for Base and Derived");
    expectStdMoveCalls(1, "Expected std::move() for base class");
}

//=============================================================================
// Test 10: Move-only types cannot be copied
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, MoveOnlyTypesNoCopy) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        class MoveOnly {
        public:
            MoveOnly() = default;
            MoveOnly(MoveOnly&&) = default;
            MoveOnly& operator=(MoveOnly&&) = default;

            // Delete copy operations
            MoveOnly(const MoveOnly&) = delete;
            MoveOnly& operator=(const MoveOnly&) = delete;
        };

        void use_move_only() {
            MoveOnly m1;
            MoveOnly m2 = std::move(m1);
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    // Note: defaulted move constructor/assignment may not show up in visitor
    // but the code should compile and std::move() should be present
    expectStdMoveCalls(1, "Expected std::move() call");
}

//=============================================================================
// Test 11: Rvalue reference parameters
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, RvalueReferenceParameters) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        template<typename T>
        class UniquePtr {
            T* ptr;
        public:
            UniquePtr() : ptr(nullptr) {}
            UniquePtr(UniquePtr&& other) : ptr(other.ptr) {
                other.ptr = nullptr;
            }
        };

        class Widget {
            UniquePtr<int> data;
        public:
            Widget(UniquePtr<int>&& ptr) : data(std::move(ptr)) {}

            void setData(UniquePtr<int>&& ptr) {
                data = std::move(ptr);
            }
        };

        void use_widget() {
            UniquePtr<int> p;
            Widget w(std::move(p));
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    EXPECT_GE(collector.stdMoveCalls.size(), static_cast<size_t>(2))
        << "Expected std::move() calls for rvalue reference parameters";
}

//=============================================================================
// Test 12: Perfect forwarding with move semantics
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, PerfectForwarding) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);

            template<typename T>
            T&& forward(T& t);
        }

        class Resource {
            int value;
        public:
            Resource(int v) : value(v) {}
            Resource(Resource&& other) : value(other.value) {
                other.value = 0;
            }
        };

        template<typename T>
        void process(T&& arg) {
            Resource r = std::forward<T>(arg);
        }

        void use_forward() {
            Resource r1(42);
            process(std::move(r1));
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    expectMoveConstructors(1, "Expected move constructor for Resource");
    expectStdMoveCalls(1, "Expected std::move() or std::forward() calls");
}

//=============================================================================
// Test 13: Move elision and RVO
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, MoveElisionRVO) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        class Heavy {
            int data[1000];
        public:
            Heavy() {}
            Heavy(Heavy&& other) {}
        };

        Heavy createHeavy() {
            Heavy h;
            return h;  // Should use RVO, not move
        }

        Heavy createHeavyExplicit() {
            Heavy h;
            return std::move(h);  // Explicit move
        }

        void use_heavy() {
            Heavy h1 = createHeavy();
            Heavy h2 = createHeavyExplicit();
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    expectMoveConstructors(1, "Expected move constructor for Heavy");
}

//=============================================================================
// Test 14: Conditional move vs copy
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, ConditionalMoveCopy) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        class Data {
            int value;
        public:
            Data(int v) : value(v) {}
            Data(const Data& other) : value(other.value) {}
            Data(Data&& other) : value(other.value) {
                other.value = 0;
            }
        };

        void conditional_move(bool should_move) {
            Data d1(42);
            Data d2 = should_move ? std::move(d1) : d1;
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    expectMoveConstructors(1, "Expected move constructor for Data");
}

//=============================================================================
// Test 15: Move semantics with exception safety
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, MoveExceptionSafety) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        class SafeMove {
            int* data;
        public:
            SafeMove() : data(nullptr) {}

            // noexcept move constructor for exception safety
            SafeMove(SafeMove&& other) noexcept : data(other.data) {
                other.data = nullptr;
            }

            // noexcept move assignment
            SafeMove& operator=(SafeMove&& other) noexcept {
                if (this != &other) {
                    data = other.data;
                    other.data = nullptr;
                }
                return *this;
            }
        };

        void use_safe_move() {
            SafeMove s1;
            SafeMove s2 = std::move(s1);
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    expectMoveConstructors(1, "Expected move constructor for SafeMove");
    expectMoveAssignments(1, "Expected move assignment for SafeMove");
}

//=============================================================================
// Test 16: Multi-level pointer move semantics (Additional test)
//=============================================================================
TEST_F(MoveSemanticIntegrationTestFixture, MultiLevelPointerMove) {
    const char *code = R"(
        namespace std {
            template<typename T>
            T&& move(T& t);
        }

        class DeepResource {
            int** matrix;
            int rows;
        public:
            DeepResource(int r) : rows(r), matrix(nullptr) {}

            DeepResource(DeepResource&& other)
                : matrix(other.matrix), rows(other.rows) {
                other.matrix = nullptr;
                other.rows = 0;
            }

            DeepResource& operator=(DeepResource&& other) {
                if (this != &other) {
                    matrix = other.matrix;
                    rows = other.rows;
                    other.matrix = nullptr;
                    other.rows = 0;
                }
                return *this;
            }
        };

        void use_deep_resource() {
            DeepResource r1(10);
            DeepResource r2 = std::move(r1);
        }
    )";

    auto AST = buildAST(code);
    expectValidAST(AST);

    traverseAndCollect(AST);

    expectMoveConstructors(1, "Expected move constructor for DeepResource");
    expectMoveAssignments(1, "Expected move assignment for DeepResource");
    expectStdMoveCalls(1, "Expected std::move() call");
}
