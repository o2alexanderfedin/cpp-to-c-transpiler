#include "StateMachine.h"
#include <cstdio>

const char* stateToString(GameState state) {
    switch (state) {
        case GameState::Menu: return "Menu";
        case GameState::Playing: return "Playing";
        case GameState::Paused: return "Paused";
        case GameState::GameOver: return "GameOver";
        default: return "Unknown";
    }
}

int main() {
    StateMachine sm(GameState::Menu);

    printf("State Machine Tests:\n");
    printf("  Initial state: %s\n", stateToString(sm.getCurrentState()));

    // Valid transitions
    sm.transition(GameState::Playing);
    printf("  After Menu -> Playing: %s\n", stateToString(sm.getCurrentState()));

    sm.transition(GameState::Paused);
    printf("  After Playing -> Paused: %s\n", stateToString(sm.getCurrentState()));

    sm.transition(GameState::Playing);
    printf("  After Paused -> Playing: %s\n", stateToString(sm.getCurrentState()));

    sm.transition(GameState::GameOver);
    printf("  After Playing -> GameOver: %s\n", stateToString(sm.getCurrentState()));

    // Invalid transition (should be ignored)
    sm.transition(GameState::Playing);
    printf("  After GameOver -> Playing (invalid): %s\n", stateToString(sm.getCurrentState()));

    // Valid transition back to menu
    sm.transition(GameState::Menu);
    printf("  After GameOver -> Menu: %s\n", stateToString(sm.getCurrentState()));

    printf("  Total valid transitions: %d\n", sm.getTransitionCount());

    // Validation
    bool passed = true;
    passed = passed && (sm.getCurrentState() == GameState::Menu);
    passed = passed && (sm.getTransitionCount() == 5);  // 5 valid transitions

    printf("\nValidation: %s\n", passed ? "PASS" : "FAIL");
    return passed ? 0 : 1;
}
