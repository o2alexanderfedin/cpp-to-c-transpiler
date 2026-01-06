/**
 * @file EnumE2ETest.cpp
 * @brief End-to-end tests for scoped enum support (Phase 47 Group 2 Task 5)
 *
 * Tests the complete pipeline with Phase 47 scoped enum features:
 * Stage 1: Clang parses C++ → C++ AST
 * Stage 2: Handlers translate C++ AST → C AST (with enum prefixing)
 * Stage 3: CodeGenerator emits C source (with prefixed enum constants)
 * Validation: Compile C code with gcc and execute
 *
 * Test Strategy:
 * - 1 active sanity test (state machine with scoped enum)
 * - 9 disabled tests (real-world enum patterns for future validation)
 *
 * Translation Pattern:
 * C++ Input:  enum class State { Idle, Running };
 *             State s = State::Idle;
 * C Output:   enum State { State__Idle, State__Running };
 *             enum State s = State__Idle;
 */

#include "dispatch/EnumTranslator.h"
#include "dispatch/FunctionHandler.h"
#include "dispatch/VariableHandler.h"
#include "dispatch/StatementHandler.h"
#include "dispatch/TypeHandler.h"
#include "dispatch/ParameterHandler.h"
#include "dispatch/CompoundStmtHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/ReturnStmtHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/BinaryOperatorHandler.h"
#include "dispatch/UnaryOperatorHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/CXXStaticCastExprHandler.h"
#include "dispatch/ConstantExprHandler.h"
#include "dispatch/ParenExprHandler.h"
#include "dispatch/ConditionalOperatorHandler.h"
#include "dispatch/CallExprHandler.h"
#include "DispatcherTestHelper.h"
#include "CodeGenerator.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>
#include <fstream>
#include <cstdlib>

using namespace cpptoc;

/**
 * @class EnumE2ETest
 * @brief Test fixture for end-to-end enum testing
 */
class EnumE2ETest : public ::testing::Test {
protected:
    // No per-test state needed - pipeline created in runPipeline

    void SetUp() override {
        // Nothing to setup - pipeline created fresh per test
    }

    /**
     * @brief Run complete pipeline: C++ source → C source → compile → execute
     * @param cppCode C++ source code
     * @param expectedExitCode Expected exit code from execution
     * @param debugOutput If true, print generated C code
     * @return true if test passed
     */
    bool runPipeline(const std::string& cppCode, int expectedExitCode, bool debugOutput = false) {
        // Stage 1 & 2: Create pipeline with dispatcher
        auto pipeline = cpptoc::test::createDispatcherPipeline(cppCode);

        // Register handlers needed for enum translation
        EnumTranslator::registerWith(*pipeline.dispatcher);
        TypeHandler::registerWith(*pipeline.dispatcher);
        FunctionHandler::registerWith(*pipeline.dispatcher);
        ParameterHandler::registerWith(*pipeline.dispatcher);
        VariableHandler::registerWith(*pipeline.dispatcher);
        StatementHandler::registerWith(*pipeline.dispatcher);
        CompoundStmtHandler::registerWith(*pipeline.dispatcher);

        // Register expression and statement handlers for complete translation
        cpptoc::DeclRefExprHandler::registerWith(*pipeline.dispatcher);
        cpptoc::ReturnStmtHandler::registerWith(*pipeline.dispatcher);
        cpptoc::LiteralHandler::registerWith(*pipeline.dispatcher);
        cpptoc::BinaryOperatorHandler::registerWith(*pipeline.dispatcher);
        cpptoc::UnaryOperatorHandler::registerWith(*pipeline.dispatcher);
        cpptoc::ImplicitCastExprHandler::registerWith(*pipeline.dispatcher);
        cpptoc::CXXStaticCastExprHandler::registerWith(*pipeline.dispatcher);
        cpptoc::ConstantExprHandler::registerWith(*pipeline.dispatcher);
        cpptoc::ParenExprHandler::registerWith(*pipeline.dispatcher);
        cpptoc::ConditionalOperatorHandler::registerWith(*pipeline.dispatcher);
        cpptoc::CallExprHandler::registerWith(*pipeline.dispatcher);

        // Stage 2: Translate all declarations via dispatcher
        for (auto* decl : pipeline.cppAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (debugOutput) {
                if (auto* enumDecl = llvm::dyn_cast<clang::EnumDecl>(decl)) {
                    std::cout << "DEBUG: Dispatching enum: " << enumDecl->getNameAsString() << "\n";
                } else if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
                    std::cout << "DEBUG: Dispatching function: " << func->getNameAsString() << "\n";
                }
            }

            // Dispatch through pipeline (handles all decl types)
            pipeline.dispatcher->dispatch(
                pipeline.cppAST->getASTContext(),
                pipeline.cAST->getASTContext(),
                const_cast<clang::Decl*>(decl)
            );
        }

        // Stage 3: Generate C code using PathMapper
        std::string cCode = cpptoc::test::generateCCode(
            pipeline.cAST->getASTContext(),
            *pipeline.pathMapper
        );

        if (debugOutput) {
            std::cout << "=== Generated C Code ===\n" << cCode << "\n=========================\n";
        }

        // Compile and execute using helper
        int actualExitCode = cpptoc::test::compileAndRun(cCode, "enum_e2e");

        if (actualExitCode == -1) {
            std::cerr << "Compilation failed\n";
            std::cerr << "Generated C code:\n" << cCode << "\n";
            return false;
        }

        return actualExitCode == expectedExitCode;
    }
};

// ============================================================================
// E2E Test 1: State Machine with Scoped Enum (ACTIVE SANITY TEST)
// ============================================================================

TEST_F(EnumE2ETest, StateMachineWithScopedEnum) {
    std::string cppCode = R"(
        enum class GameState {
            Menu,
            Playing,
            Paused,
            GameOver
        };

        int getStateCode(GameState state) {
            switch (state) {
                case GameState::Menu:
                    return 0;
                case GameState::Playing:
                    return 1;
                case GameState::Paused:
                    return 2;
                case GameState::GameOver:
                    return 3;
            }
            return -1;
        }

        int main() {
            GameState state = GameState::Playing;
            return getStateCode(state);  // Should return 1
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 1, true))  // Enable debug to see generated code
        << "Expected exit code 1 (Playing state)";
}

// ============================================================================
// E2E Test 2: HTTP Status Codes with Type Specification (DISABLED)
// ============================================================================

TEST_F(EnumE2ETest, HttpStatusCodesWithTypes) {
    std::string cppCode = R"(
        enum class HttpStatus : unsigned short {
            OK = 200,
            Created = 201,
            NoContent = 204,
            BadRequest = 400,
            NotFound = 404,
            InternalError = 500
        };

        int isSuccess(HttpStatus status) {
            switch (status) {
                case HttpStatus::OK:
                case HttpStatus::Created:
                case HttpStatus::NoContent:
                    return 1;
                case HttpStatus::BadRequest:
                case HttpStatus::NotFound:
                case HttpStatus::InternalError:
                    return 0;
            }
            return -1;
        }

        int main() {
            HttpStatus status = HttpStatus::OK;
            return isSuccess(status);  // Should return 1 (success)
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 1))
        << "Expected exit code 1 (HTTP OK is success)";
}

// ============================================================================
// E2E Test 3: Error Handling with Result Pattern (DISABLED)
// ============================================================================

TEST_F(EnumE2ETest, ErrorHandlingResultPattern) {
    std::string cppCode = R"(
        enum class Result : int {
            Success = 0,
            ErrorNotFound = -1,
            ErrorPermission = -2,
            ErrorInvalidArg = -3,
            ErrorOutOfMemory = -4
        };

        Result validateInput(int value) {
            if (value < 0) {
                return Result::ErrorInvalidArg;
            }
            if (value > 100) {
                return Result::ErrorOutOfMemory;
            }
            return Result::Success;
        }

        int main() {
            Result r = validateInput(50);
            return (r == Result::Success) ? 0 : -1;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 0))
        << "Expected exit code 0 (Success result)";
}

// ============================================================================
// E2E Test 4: Flags/Bitmask Enum (DISABLED)
// ============================================================================

TEST_F(EnumE2ETest, FlagsBitmaskEnum) {
    std::string cppCode = R"(
        // Note: Using scoped enum with bitwise operations
        enum class FilePermissions : unsigned int {
            None = 0,
            Read = 1,
            Write = 2,
            Execute = 4,
            ReadWrite = 3,    // Read | Write
            All = 7           // Read | Write | Execute
        };

        int hasPermission(FilePermissions perms, FilePermissions required) {
            unsigned int p = static_cast<unsigned int>(perms);
            unsigned int r = static_cast<unsigned int>(required);
            return (p & r) == r ? 1 : 0;
        }

        int main() {
            FilePermissions perms = FilePermissions::ReadWrite;
            FilePermissions check = FilePermissions::Read;
            return hasPermission(perms, check);  // Should return 1 (has read)
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 1))
        << "Expected exit code 1 (has read permission)";
}

// ============================================================================
// E2E Test 5: State Machine with Transitions (DISABLED)
// ============================================================================

TEST_F(EnumE2ETest, StateMachineTransitions) {
    std::string cppCode = R"(
        enum class State : unsigned char {
            Idle,
            Starting,
            Running,
            Stopping,
            Stopped
        };

        State transition(State current, int event) {
            switch (current) {
                case State::Idle:
                    if (event == 1) return State::Starting;
                    break;
                case State::Starting:
                    if (event == 2) return State::Running;
                    break;
                case State::Running:
                    if (event == 3) return State::Stopping;
                    break;
                case State::Stopping:
                    if (event == 4) return State::Stopped;
                    break;
                case State::Stopped:
                    if (event == 0) return State::Idle;
                    break;
            }
            return current;
        }

        int main() {
            State s = State::Idle;
            s = transition(s, 1);  // Idle → Starting
            s = transition(s, 2);  // Starting → Running

            // Return 2 if in Running state
            return (s == State::Running) ? 2 : 0;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 2))
        << "Expected exit code 2 (Running state)";
}

// ============================================================================
// E2E Test 6: Menu System with Nested States (DISABLED)
// ============================================================================

TEST_F(EnumE2ETest, MenuSystemNestedStates) {
    std::string cppCode = R"(
        enum class MenuState {
            MainMenu,
            SettingsMenu,
            GraphicsSettings,
            AudioSettings,
            GameplaySettings,
            CreditsScreen
        };

        int getMenuDepth(MenuState menu) {
            switch (menu) {
                case MenuState::MainMenu:
                    return 0;
                case MenuState::SettingsMenu:
                case MenuState::CreditsScreen:
                    return 1;
                case MenuState::GraphicsSettings:
                case MenuState::AudioSettings:
                case MenuState::GameplaySettings:
                    return 2;
            }
            return -1;
        }

        int main() {
            MenuState menu = MenuState::GraphicsSettings;
            return getMenuDepth(menu);  // Should return 2
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 2))
        << "Expected exit code 2 (menu depth 2)";
}

// ============================================================================
// E2E Test 7: Priority Queue with Enum Priorities (DISABLED)
// ============================================================================

TEST_F(EnumE2ETest, PriorityQueueEnumPriorities) {
    std::string cppCode = R"(
        enum class Priority : int {
            Critical = 10,
            High = 5,
            Normal = 0,
            Low = -5,
            Deferred = -10
        };

        int comparePriority(Priority p1, Priority p2) {
            int v1 = static_cast<int>(p1);
            int v2 = static_cast<int>(p2);
            if (v1 > v2) return 1;
            if (v1 < v2) return -1;
            return 0;
        }

        int main() {
            Priority p1 = Priority::Critical;
            Priority p2 = Priority::Normal;
            return comparePriority(p1, p2);  // Should return 1 (Critical > Normal)
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 1))
        << "Expected exit code 1 (Critical > Normal)";
}

// ============================================================================
// E2E Test 8: Color Palette with RGB Enums (DISABLED)
// ============================================================================

TEST_F(EnumE2ETest, ColorPaletteRGBEnums) {
    std::string cppCode = R"(
        enum class Color : unsigned char {
            Red = 0,
            Green = 1,
            Blue = 2,
            Yellow = 3,
            Magenta = 4,
            Cyan = 5,
            White = 6,
            Black = 7
        };

        int isPrimaryColor(Color c) {
            switch (c) {
                case Color::Red:
                case Color::Green:
                case Color::Blue:
                    return 1;
                default:
                    return 0;
            }
        }

        int main() {
            Color c = Color::Blue;
            return isPrimaryColor(c);  // Should return 1 (Blue is primary)
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 1))
        << "Expected exit code 1 (Blue is primary color)";
}

// ============================================================================
// E2E Test 9: Game Input Handling (DISABLED)
// ============================================================================

TEST_F(EnumE2ETest, GameInputHandling) {
    std::string cppCode = R"(
        enum class Input : unsigned char {
            None = 0,
            Up = 1,
            Down = 2,
            Left = 3,
            Right = 4,
            ButtonA = 5,
            ButtonB = 6,
            Start = 7,
            Select = 8
        };

        int isDirectional(Input input) {
            switch (input) {
                case Input::Up:
                case Input::Down:
                case Input::Left:
                case Input::Right:
                    return 1;
                default:
                    return 0;
            }
        }

        int main() {
            Input input = Input::Left;
            return isDirectional(input);  // Should return 1 (Left is directional)
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 1))
        << "Expected exit code 1 (Left is directional input)";
}

// ============================================================================
// E2E Test 10: Mixed Scoped and Unscoped Enums (DISABLED)
// ============================================================================

TEST_F(EnumE2ETest, MixedScopedAndUnscopedEnums) {
    std::string cppCode = R"(
        // Unscoped enum (C-compatible)
        enum Color {
            Red,
            Green,
            Blue
        };

        // Scoped enum (C++ only, translated with prefix)
        enum class Status : int {
            OK = 0,
            Warning = 1,
            Error = 2
        };

        int getCode(Color c, Status s) {
            int colorValue = c;  // Unscoped: direct access
            int statusValue = static_cast<int>(s);  // Scoped: needs prefix translation
            return colorValue + statusValue;
        }

        int main() {
            Color c = Green;  // No prefix
            Status s = Status::OK;  // With prefix
            return getCode(c, s);  // Should return 1 (Green=1, OK=0)
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 1))
        << "Expected exit code 1 (Green=1 + OK=0)";
}

// ============================================================================
// Summary
// ============================================================================

/*
 * Phase 47 E2E Test Summary:
 *
 * Total Tests: 10
 * - Active: 1 (StateMachineWithScopedEnum)
 * - Disabled: 9 (real-world patterns for future validation)
 *
 * Test Coverage:
 * 1. ✅ State machine with scoped enum (ACTIVE)
 * 2. ❌ HTTP status codes with type specification (DISABLED)
 * 3. ❌ Error handling with Result pattern (DISABLED)
 * 4. ❌ Flags/bitmask enum (DISABLED)
 * 5. ❌ State machine with transitions (DISABLED)
 * 6. ❌ Menu system with nested states (DISABLED)
 * 7. ❌ Priority queue with enum priorities (DISABLED)
 * 8. ❌ Color palette with RGB enums (DISABLED)
 * 9. ❌ Game input handling (DISABLED)
 * 10. ❌ Mixed scoped and unscoped enums (DISABLED)
 *
 * Pipeline Validation:
 * - Stage 1: Clang parses C++ → C++ AST
 * - Stage 2: Handlers translate C++ AST → C AST
 *   - Scoped enum: enum class X → enum X (with prefixed constants)
 *   - Enum constant: X::Value → X__Value
 * - Stage 3: CodeGenerator emits C code
 * - Validation: gcc compiles and executes successfully
 *
 * Next Steps:
 * - Enable tests as enum translation features are completed
 * - Add type specification support (Tasks 1-2)
 * - Extract EnumTranslator handler (Tasks 6-7)
 * - Gradually enable disabled tests as features mature
 */
