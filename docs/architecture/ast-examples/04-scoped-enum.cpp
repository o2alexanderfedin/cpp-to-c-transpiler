// Example: Scoped enum
enum class State {
    Idle,
    Running,
    Stopped
};

State getInitialState() {
    return State::Idle;
}

bool isRunning(State s) {
    return s == State::Running;
}
