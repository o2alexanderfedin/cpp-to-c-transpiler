/**
 * @file StructsE2ETest.cpp
 * @brief End-to-end tests for structs (C-style)
 *
 * Tests the full pipeline with Phase 43 features:
 * Stage 1: Clang parses C++ → C++ AST
 * Stage 2: Handlers translate C++ AST → C AST
 * Stage 3: CodeGenerator emits C source
 * Validation: Compile C code with gcc and execute
 */

#include "tests/fixtures/DispatcherTestHelper.h"
#include "dispatch/TypeHandler.h"
#include "dispatch/ParameterHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/MemberExprHandler.h"
#include "dispatch/BinaryOperatorHandler.h"
#include "dispatch/UnaryOperatorHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/ParenExprHandler.h"
#include "dispatch/CallExprHandler.h"
#include "dispatch/ArraySubscriptExprHandler.h"
#include "dispatch/CompoundStmtHandler.h"
#include "dispatch/DeclStmtHandler.h"
#include "dispatch/ReturnStmtHandler.h"
#include "dispatch/StatementHandler.h"
#include "dispatch/RecordHandler.h"
#include "dispatch/FunctionHandler.h"
#include "dispatch/VariableHandler.h"
#include "dispatch/TranslationUnitHandler.h"
#include <gtest/gtest.h>

using namespace cpptoc;

/**
 * @class StructsE2ETest
 * @brief Test fixture for end-to-end structs testing
 */
class StructsE2ETest : public ::testing::Test {
protected:
    /**
     * @brief Run complete pipeline: C++ source → C source → compile → execute
     * @param cppCode C++ source code
     * @param expectedExitCode Expected exit code from execution
     * @return true if test passed
     */
    bool runPipeline(const std::string& cppCode, int expectedExitCode) {
        // Create dispatcher pipeline
        auto pipeline = cpptoc::test::createDispatcherPipeline(cppCode);

        // Register handlers needed for struct tests
        // Base handlers first
        TypeHandler::registerWith(*pipeline.dispatcher);
        ParameterHandler::registerWith(*pipeline.dispatcher);

        // Expression handlers (including struct member access)
        LiteralHandler::registerWith(*pipeline.dispatcher);
        DeclRefExprHandler::registerWith(*pipeline.dispatcher);
        MemberExprHandler::registerWith(*pipeline.dispatcher);  // For struct.field access
        BinaryOperatorHandler::registerWith(*pipeline.dispatcher);
        UnaryOperatorHandler::registerWith(*pipeline.dispatcher);
        ImplicitCastExprHandler::registerWith(*pipeline.dispatcher);
        ParenExprHandler::registerWith(*pipeline.dispatcher);
        CallExprHandler::registerWith(*pipeline.dispatcher);
        ArraySubscriptExprHandler::registerWith(*pipeline.dispatcher);

        // Statement handlers
        CompoundStmtHandler::registerWith(*pipeline.dispatcher);
        DeclStmtHandler::registerWith(*pipeline.dispatcher);
        ReturnStmtHandler::registerWith(*pipeline.dispatcher);
        StatementHandler::registerWith(*pipeline.dispatcher);

        // Declaration handlers
        RecordHandler::registerWith(*pipeline.dispatcher);  // Handles struct definitions
        FunctionHandler::registerWith(*pipeline.dispatcher);
        VariableHandler::registerWith(*pipeline.dispatcher);
        TranslationUnitHandler::registerWith(*pipeline.dispatcher);

        // Dispatch the TranslationUnit (dispatches all top-level declarations recursively)
        auto* TU = pipeline.cppAST->getASTContext().getTranslationUnitDecl();
        pipeline.dispatcher->dispatch(
            pipeline.cppAST->getASTContext(),
            pipeline.cAST->getASTContext(),
            TU
        );

        // Generate C code from C AST using PathMapper
        std::string cCode = cpptoc::test::generateCCode(
            pipeline.cAST->getASTContext(),
            *pipeline.pathMapper
        );

        // Compile and run
        int actualExitCode = cpptoc::test::compileAndRun(cCode, "e2e_structs");

        if (actualExitCode == -1) {
            std::cerr << "Compilation failed!\n";
            std::cerr << "Generated C code:\n" << cCode << "\n";
            return false;
        }

        return actualExitCode == expectedExitCode;
    }
};

// ============================================================================
// E2E Test 1: Simple Struct Creation and Usage
// ============================================================================

TEST_F(StructsE2ETest, SimpleStructCreationAndUsage) {
    std::string cppCode = R"(
        struct Point {
            int x;
            int y;
        };

        int main() {
            Point p;
            p.x = 5;
            p.y = 3;
            return p.x + p.y;  // Returns 8
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 8)) << "Expected exit code 8 (sum of x and y)";
}

// ============================================================================
// E2E Test 2: Struct Initialization and Field Access
// ============================================================================

TEST_F(StructsE2ETest, DISABLED_StructInitializationAndFieldAccess) {
    std::string cppCode = R"(
        struct Rectangle {
            int width;
            int height;
        };

        int calculateArea(Rectangle rect) {
            return rect.width * rect.height;
        }

        int main() {
            Rectangle r = {4, 5};
            return calculateArea(r);  // Returns 20
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 20)) << "Expected exit code 20 (rectangle area)";
}

// ============================================================================
// E2E Test 3: Linked List Implementation
// ============================================================================

TEST_F(StructsE2ETest, DISABLED_LinkedListImplementation) {
    std::string cppCode = R"(
        struct Node {
            int data;
            Node* next;
        };

        int sumList(Node* head) {
            int sum = 0;
            Node* current = head;
            while (current != 0) {
                sum = sum + current->data;
                current = current->next;
            }
            return sum;
        }

        int main() {
            Node third = {30, 0};
            Node second = {20, &third};
            Node first = {10, &second};
            return sumList(&first);  // Returns 60
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 60)) << "Expected exit code 60 (linked list sum)";
}

// ============================================================================
// E2E Test 4: Binary Tree Operations
// ============================================================================

TEST_F(StructsE2ETest, DISABLED_BinaryTreeOperations) {
    std::string cppCode = R"(
        struct TreeNode {
            int value;
            TreeNode* left;
            TreeNode* right;
        };

        int countNodes(TreeNode* root) {
            if (root == 0) {
                return 0;
            }
            return 1 + countNodes(root->left) + countNodes(root->right);
        }

        int main() {
            TreeNode left = {2, 0, 0};
            TreeNode right = {3, 0, 0};
            TreeNode root = {1, &left, &right};
            return countNodes(&root);  // Returns 3
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 3)) << "Expected exit code 3 (tree node count)";
}

// ============================================================================
// E2E Test 5: Point/Rectangle Geometry Calculations
// ============================================================================

TEST_F(StructsE2ETest, DISABLED_PointRectangleGeometry) {
    std::string cppCode = R"(
        struct Point {
            int x;
            int y;
        };

        struct Rectangle {
            Point topLeft;
            Point bottomRight;
        };

        int calculateRectangleArea(Rectangle rect) {
            int width = rect.bottomRight.x - rect.topLeft.x;
            int height = rect.bottomRight.y - rect.topLeft.y;
            return width * height;
        }

        int main() {
            Point tl = {0, 0};
            Point br = {5, 4};
            Rectangle rect = {tl, br};
            return calculateRectangleArea(rect);  // Returns 20
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 20)) << "Expected exit code 20 (nested struct area calculation)";
}

// ============================================================================
// E2E Test 6: Color Manipulation
// ============================================================================

TEST_F(StructsE2ETest, DISABLED_ColorManipulation) {
    std::string cppCode = R"(
        struct Color {
            int red;
            int green;
            int blue;
        };

        int brightness(Color c) {
            return (c.red + c.green + c.blue) / 3;
        }

        int main() {
            Color purple = {128, 0, 128};
            return brightness(purple);  // Returns 85 (integer division)
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 85)) << "Expected exit code 85 (average color brightness)";
}

// ============================================================================
// E2E Test 7: Student Record Management
// ============================================================================

TEST_F(StructsE2ETest, StudentRecordManagement) {
    std::string cppCode = R"(
        struct Student {
            int id;
            int grade;
            int age;
        };

        int averageGrade(Student* students, int count) {
            int sum = 0;
            for (int i = 0; i < count; i = i + 1) {
                sum = sum + students[i].grade;
            }
            return sum / count;
        }

        int main() {
            Student students[3];
            students[0].id = 1;
            students[0].grade = 85;
            students[0].age = 20;

            students[1].id = 2;
            students[1].grade = 90;
            students[1].age = 21;

            students[2].id = 3;
            students[2].grade = 78;
            students[2].age = 19;

            return averageGrade(students, 3);  // Returns 84
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 84)) << "Expected exit code 84 (average student grade)";
}

// ============================================================================
// E2E Test 8: 2D Vector Operations
// ============================================================================

TEST_F(StructsE2ETest, DISABLED_Vector2DOperations) {
    std::string cppCode = R"(
        struct Vector2D {
            int x;
            int y;
        };

        int dotProduct(Vector2D a, Vector2D b) {
            return a.x * b.x + a.y * b.y;
        }

        Vector2D addVectors(Vector2D a, Vector2D b) {
            Vector2D result;
            result.x = a.x + b.x;
            result.y = a.y + b.y;
            return result;
        }

        int main() {
            Vector2D v1 = {3, 4};
            Vector2D v2 = {2, 1};
            int dot = dotProduct(v1, v2);  // 3*2 + 4*1 = 10
            Vector2D sum = addVectors(v1, v2);  // {5, 5}
            return dot + sum.x;  // 10 + 5 = 15
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 15)) << "Expected exit code 15 (dot product + sum.x)";
}

// ============================================================================
// E2E Test 9: Stack Implementation with Struct
// ============================================================================

TEST_F(StructsE2ETest, StackImplementation) {
    std::string cppCode = R"(
        struct Stack {
            int data[10];
            int top;
        };

        void push(Stack* s, int value) {
            if (s->top < 10) {
                s->data[s->top] = value;
                s->top = s->top + 1;
            }
        }

        int pop(Stack* s) {
            if (s->top > 0) {
                s->top = s->top - 1;
                return s->data[s->top];
            }
            return -1;
        }

        int main() {
            Stack s;
            s.top = 0;
            push(&s, 10);
            push(&s, 20);
            push(&s, 30);
            int val1 = pop(&s);  // 30
            int val2 = pop(&s);  // 20
            return val1 + val2;  // Returns 50
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 50)) << "Expected exit code 50 (stack operations)";
}

// ============================================================================
// E2E Test 10: Queue Implementation with Struct
// ============================================================================

TEST_F(StructsE2ETest, QueueImplementation) {
    std::string cppCode = R"(
        struct Queue {
            int data[10];
            int front;
            int rear;
            int size;
        };

        void enqueue(Queue* q, int value) {
            if (q->size < 10) {
                q->data[q->rear] = value;
                q->rear = (q->rear + 1) % 10;
                q->size = q->size + 1;
            }
        }

        int dequeue(Queue* q) {
            if (q->size > 0) {
                int value = q->data[q->front];
                q->front = (q->front + 1) % 10;
                q->size = q->size - 1;
                return value;
            }
            return -1;
        }

        int main() {
            Queue q;
            q.front = 0;
            q.rear = 0;
            q.size = 0;

            enqueue(&q, 5);
            enqueue(&q, 10);
            enqueue(&q, 15);

            int val1 = dequeue(&q);  // 5
            int val2 = dequeue(&q);  // 10
            return val1 + val2;  // Returns 15
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 15)) << "Expected exit code 15 (queue operations)";
}

// ============================================================================
// E2E Test 11: Distance Calculation Between Points
// ============================================================================

TEST_F(StructsE2ETest, DISABLED_DistanceCalculation) {
    std::string cppCode = R"(
        struct Point {
            int x;
            int y;
        };

        int distanceSquared(Point a, Point b) {
            int dx = b.x - a.x;
            int dy = b.y - a.y;
            return dx * dx + dy * dy;
        }

        int main() {
            Point p1 = {0, 0};
            Point p2 = {3, 4};
            return distanceSquared(p1, p2);  // Returns 25 (3^2 + 4^2)
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 25)) << "Expected exit code 25 (distance squared)";
}

// ============================================================================
// E2E Test 12: Struct Array Manipulation
// ============================================================================

TEST_F(StructsE2ETest, StructArrayManipulation) {
    std::string cppCode = R"(
        struct Score {
            int value;
            int multiplier;
        };

        int totalScore(Score* scores, int count) {
            int total = 0;
            for (int i = 0; i < count; i = i + 1) {
                total = total + scores[i].value * scores[i].multiplier;
            }
            return total;
        }

        int main() {
            Score scores[4];
            scores[0].value = 10;
            scores[0].multiplier = 2;
            scores[1].value = 5;
            scores[1].multiplier = 3;
            scores[2].value = 8;
            scores[2].multiplier = 1;
            scores[3].value = 3;
            scores[3].multiplier = 4;

            return totalScore(scores, 4);  // 10*2 + 5*3 + 8*1 + 3*4 = 55
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 55)) << "Expected exit code 55 (weighted score sum)";
}

// ============================================================================
// Basic Sanity Test (infrastructure verification)
// ============================================================================

TEST_F(StructsE2ETest, BasicSanity) {
    // Just verify test infrastructure works
    EXPECT_TRUE(true);
}
