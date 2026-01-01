/**
 * @file StructsIntegrationTest.cpp
 * @brief Integration tests for C-style structs and struct operations
 *
 * Tests Phase 43 features working together with Phase 1-4 features:
 * - Struct declarations (C-style, no methods)
 * - Field access (. operator)
 * - Pointer field access (-> operator)
 * - Struct initialization (brace-init)
 * - Struct parameters and return values
 * - Nested structs
 * - Integration with control flow, arrays, and pointers
 */

#include "dispatch/FunctionHandler.h"
#include "dispatch/VariableHandler.h"
#include "dispatch/StatementHandler.h"
#include "dispatch/RecordHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class StructsIntegrationTest
 * @brief Test fixture for Phase 43 integration testing
 */
class StructsIntegrationTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    std::unique_ptr<FunctionHandler> funcHandler;
    std::unique_ptr<VariableHandler> varHandler;
    std::unique_ptr<ExpressionHandler> exprHandler;
    std::unique_ptr<StatementHandler> stmtHandler;
    std::unique_ptr<RecordHandler> recordHandler;

    void SetUp() override {
        // Create real AST contexts
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr);
        ASSERT_NE(cAST, nullptr);

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Create all handlers
        funcHandler = std::make_unique<FunctionHandler>();
        varHandler = std::make_unique<VariableHandler>();
        exprHandler = std::make_unique<ExpressionHandler>();
        stmtHandler = std::make_unique<StatementHandler>();
        recordHandler = std::make_unique<RecordHandler>();
    }

    void TearDown() override {
        recordHandler.reset();
        stmtHandler.reset();
        exprHandler.reset();
        varHandler.reset();
        funcHandler.reset();
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Helper to translate a function by name
     */
    clang::FunctionDecl* translateFunction(const std::string& code, const std::string& funcName) {
        auto testAST = clang::tooling::buildASTFromCode(code);
        if (!testAST) return nullptr;

        clang::FunctionDecl* cppFunc = nullptr;
        for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
                if (func->getNameAsString() == funcName) {
                    cppFunc = func;
                    break;
                }
            }
        }

        if (!cppFunc) return nullptr;

        return llvm::dyn_cast<clang::FunctionDecl>(
            funcHandler->handleDecl(cppFunc, *context)
        );
    }
};

// ============================================================================
// Struct Creation and Initialization Integration Tests (5 tests)
// ============================================================================

TEST_F(StructsIntegrationTest, FunctionCreatingAndReturningStruct) {
    // Test: Function that creates and returns a struct
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        Point create_point(int x, int y) {
            Point p;
            p.x = x;
            p.y = y;
            return p;
        }
    )";

    auto* cFunc = translateFunction(code, "create_point");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "create_point");
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

TEST_F(StructsIntegrationTest, FunctionWithStructInitialization) {
    // Test: Function using brace initialization
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        Point make_origin() {
            Point p = {0, 0};
            return p;
        }
    )";

    auto* cFunc = translateFunction(code, "make_origin");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, FunctionWithPartialStructInit) {
    // Test: Partial struct initialization
    std::string code = R"(
        struct Color {
            int r;
            int g;
            int b;
            int a;
        };

        Color make_red() {
            Color c = {255, 0, 0, 255};
            return c;
        }
    )";

    auto* cFunc = translateFunction(code, "make_red");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, FunctionWithNestedStructInit) {
    // Test: Nested struct initialization
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        struct Rectangle {
            Point topLeft;
            Point bottomRight;
        };

        Rectangle make_rect(int x1, int y1, int x2, int y2) {
            Rectangle r;
            r.topLeft.x = x1;
            r.topLeft.y = y1;
            r.bottomRight.x = x2;
            r.bottomRight.y = y2;
            return r;
        }
    )";

    auto* cFunc = translateFunction(code, "make_rect");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 4);
}

TEST_F(StructsIntegrationTest, StructInitializationInLoop) {
    // Test: Struct initialization inside loop
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        void fill_points(Point* arr, int size) {
            for (int i = 0; i < size; i++) {
                Point p = {i, i * 2};
                arr[i] = p;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "fill_points");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Struct Field Modification Integration Tests (4 tests)
// ============================================================================

TEST_F(StructsIntegrationTest, FunctionModifyingStructFields) {
    // Test: Function modifying struct fields
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        void translate_point(Point* p, int dx, int dy) {
            p->x = p->x + dx;
            p->y = p->y + dy;
        }
    )";

    auto* cFunc = translateFunction(code, "translate_point");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 3);
}

TEST_F(StructsIntegrationTest, StructFieldIncrementInLoop) {
    // Test: Modifying struct fields in loop
    std::string code = R"(
        struct Counter {
            int count;
            int step;
        };

        void increment_n_times(Counter* c, int n) {
            for (int i = 0; i < n; i++) {
                c->count = c->count + c->step;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "increment_n_times");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, ConditionalFieldModification) {
    // Test: Conditional modification of struct fields
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        void clamp_point(Point* p, int max_val) {
            if (p->x > max_val) {
                p->x = max_val;
            }
            if (p->y > max_val) {
                p->y = max_val;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "clamp_point");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, SwapStructFields) {
    // Test: Swap fields between two structs
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        void swap_points(Point* a, Point* b) {
            int temp_x = a->x;
            int temp_y = a->y;
            a->x = b->x;
            a->y = b->y;
            b->x = temp_x;
            b->y = temp_y;
        }
    )";

    auto* cFunc = translateFunction(code, "swap_points");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Linked List Operations Integration Tests (3 tests)
// ============================================================================

TEST_F(StructsIntegrationTest, LinkedListNodeStruct) {
    // Test: Simple linked list node
    std::string code = R"(
        struct Node {
            int value;
            Node* next;
        };

        Node* create_node(int val) {
            Node* n = 0;
            // Would normally allocate memory here
            return n;
        }
    )";

    auto* cFunc = translateFunction(code, "create_node");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, LinkedListTraversal) {
    // Test: Traverse linked list and count nodes
    std::string code = R"(
        struct Node {
            int value;
            Node* next;
        };

        int count_nodes(Node* head) {
            int count = 0;
            Node* current = head;
            while (current != 0) {
                count++;
                current = current->next;
            }
            return count;
        }
    )";

    auto* cFunc = translateFunction(code, "count_nodes");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, LinkedListSum) {
    // Test: Sum values in linked list
    std::string code = R"(
        struct Node {
            int value;
            Node* next;
        };

        int sum_list(Node* head) {
            int sum = 0;
            while (head != 0) {
                sum = sum + head->value;
                head = head->next;
            }
            return sum;
        }
    )";

    auto* cFunc = translateFunction(code, "sum_list");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Struct Arrays and Iteration Integration Tests (4 tests)
// ============================================================================

TEST_F(StructsIntegrationTest, StructArrayIteration) {
    // Test: Iterate over struct array
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        int sum_x_coords(Point* points, int count) {
            int sum = 0;
            for (int i = 0; i < count; i++) {
                sum = sum + points[i].x;
            }
            return sum;
        }
    )";

    auto* cFunc = translateFunction(code, "sum_x_coords");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, StructArrayModification) {
    // Test: Modify all structs in array
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        void offset_points(Point* points, int count, int offset) {
            for (int i = 0; i < count; i++) {
                points[i].x = points[i].x + offset;
                points[i].y = points[i].y + offset;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "offset_points");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, FindStructInArray) {
    // Test: Find struct matching condition
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        Point* find_point(Point* points, int count, int target_x) {
            for (int i = 0; i < count; i++) {
                if (points[i].x == target_x) {
                    return &points[i];
                }
            }
            return 0;
        }
    )";

    auto* cFunc = translateFunction(code, "find_point");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, CopyStructArray) {
    // Test: Copy struct array
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        void copy_points(Point* dest, const Point* src, int count) {
            for (int i = 0; i < count; i++) {
                dest[i].x = src[i].x;
                dest[i].y = src[i].y;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "copy_points");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Nested Struct Access Integration Tests (3 tests)
// ============================================================================

TEST_F(StructsIntegrationTest, NestedStructAccess) {
    // Test: Access nested struct fields
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        struct Rectangle {
            Point topLeft;
            Point bottomRight;
        };

        int get_width(Rectangle* rect) {
            return rect->bottomRight.x - rect->topLeft.x;
        }
    )";

    auto* cFunc = translateFunction(code, "get_width");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, DeepNestedAccess) {
    // Test: Deep nested struct access
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        struct Rectangle {
            Point topLeft;
            Point bottomRight;
        };

        struct Scene {
            Rectangle bounds;
            int objectCount;
        };

        int get_scene_width(Scene* scene) {
            return scene->bounds.bottomRight.x - scene->bounds.topLeft.x;
        }
    )";

    auto* cFunc = translateFunction(code, "get_scene_width");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, ModifyNestedStructField) {
    // Test: Modify deeply nested field
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        struct Rectangle {
            Point topLeft;
            Point bottomRight;
        };

        void move_rectangle(Rectangle* rect, int dx, int dy) {
            rect->topLeft.x = rect->topLeft.x + dx;
            rect->topLeft.y = rect->topLeft.y + dy;
            rect->bottomRight.x = rect->bottomRight.x + dx;
            rect->bottomRight.y = rect->bottomRight.y + dy;
        }
    )";

    auto* cFunc = translateFunction(code, "move_rectangle");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Struct Parameters vs Pointers Integration Tests (3 tests)
// ============================================================================

TEST_F(StructsIntegrationTest, StructPassedByValue) {
    // Test: Struct passed by value
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        int get_distance_squared(Point p1, Point p2) {
            int dx = p2.x - p1.x;
            int dy = p2.y - p1.y;
            return dx * dx + dy * dy;
        }
    )";

    auto* cFunc = translateFunction(code, "get_distance_squared");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

TEST_F(StructsIntegrationTest, StructPassedByPointer) {
    // Test: Struct passed by pointer (const)
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        int get_manhattan_distance(const Point* p1, const Point* p2) {
            int dx = p2->x - p1->x;
            int dy = p2->y - p1->y;
            if (dx < 0) dx = -dx;
            if (dy < 0) dy = -dy;
            return dx + dy;
        }
    )";

    auto* cFunc = translateFunction(code, "get_manhattan_distance");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, MixedStructParameters) {
    // Test: Mix of value and pointer parameters
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        void add_to_point(Point* dest, Point offset) {
            dest->x = dest->x + offset.x;
            dest->y = dest->y + offset.y;
        }
    )";

    auto* cFunc = translateFunction(code, "add_to_point");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Complex Struct Types Integration Tests (3 tests)
// ============================================================================

TEST_F(StructsIntegrationTest, StructWithAllPrimitiveTypes) {
    // Test: Struct with various primitive types
    std::string code = R"(
        struct AllTypes {
            int i;
            float f;
            double d;
            char c;
        };

        int check_struct(AllTypes* at) {
            if (at->i > 0 && at->c != 0) {
                return 1;
            }
            return 0;
        }
    )";

    auto* cFunc = translateFunction(code, "check_struct");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, StructWithMixedTypes) {
    // Test: Struct with primitives, arrays, and pointers
    std::string code = R"(
        struct ComplexStruct {
            int id;
            int values[5];
            int* ptr;
        };

        int sum_struct_values(ComplexStruct* cs) {
            int sum = cs->id;
            for (int i = 0; i < 5; i++) {
                sum = sum + cs->values[i];
            }
            if (cs->ptr != 0) {
                sum = sum + *cs->ptr;
            }
            return sum;
        }
    )";

    auto* cFunc = translateFunction(code, "sum_struct_values");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(StructsIntegrationTest, MultipleStructTypesInFunction) {
    // Test: Function using multiple struct types
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };

        struct Color {
            int r;
            int g;
            int b;
        };

        struct Pixel {
            Point pos;
            Color color;
        };

        int is_red_pixel(Pixel* px) {
            if (px->color.r > 200 && px->color.g < 50 && px->color.b < 50) {
                return 1;
            }
            return 0;
        }
    )";

    auto* cFunc = translateFunction(code, "is_red_pixel");
    ASSERT_NE(cFunc, nullptr);
}
