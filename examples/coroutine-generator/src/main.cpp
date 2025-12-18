// Coroutine Generator Example
// Demonstrates C++20 coroutines transpiled to state machines

#include <cstdio>
#include <cstdlib>
#include <cstring>

// ============================================================================
// Coroutine Frame (transpiler generates this)
// ============================================================================

enum CoroutineState {
    STATE_START = 0,
    STATE_SUSPENDED = 1,
    STATE_DONE = 2
};

// ============================================================================
// Simple Generator (Manual State Machine Implementation)
// ============================================================================

// In real transpiler output, this would be generated from:
// generator<int> counter(int max) {
//     for (int i = 0; i < max; i++) {
//         co_yield i;
//     }
// }

struct CounterFrame {
    CoroutineState state;
    int max;           // Parameter
    int i;             // Loop variable
    int current_value; // Yielded value
};

struct Counter {
    CounterFrame* frame;

    Counter(int max) {
        frame = (CounterFrame*)malloc(sizeof(CounterFrame));
        frame->state = STATE_START;
        frame->max = max;
        frame->i = 0;
        frame->current_value = 0;
    }

    ~Counter() {
        if (frame) {
            free(frame);
        }
    }

    bool next() {
        if (frame->state == STATE_DONE) {
            return false;
        }

        // State machine resume
        switch (frame->state) {
            case STATE_START:
                frame->i = 0;
                goto check_loop;

            case STATE_SUSPENDED:
                frame->i++;
                goto check_loop;

            case STATE_DONE:
                return false;
        }

    check_loop:
        if (frame->i < frame->max) {
            frame->current_value = frame->i;
            frame->state = STATE_SUSPENDED;
            return true;
        } else {
            frame->state = STATE_DONE;
            return false;
        }
    }

    int value() const {
        return frame->current_value;
    }
};

// ============================================================================
// Fibonacci Generator
// ============================================================================

struct FibonacciFrame {
    CoroutineState state;
    int limit;
    int a, b;
    int current_value;
};

struct Fibonacci {
    FibonacciFrame* frame;

    Fibonacci(int max_count) {
        frame = (FibonacciFrame*)malloc(sizeof(FibonacciFrame));
        frame->state = STATE_START;
        frame->limit = max_count;
        frame->a = 0;
        frame->b = 1;
        frame->current_value = 0;
    }

    ~Fibonacci() {
        if (frame) {
            free(frame);
        }
    }

    bool next() {
        if (frame->state == STATE_DONE) {
            return false;
        }

        switch (frame->state) {
            case STATE_START:
                frame->a = 0;
                frame->b = 1;
                frame->limit--;
                frame->current_value = frame->a;
                frame->state = STATE_SUSPENDED;
                return true;

            case STATE_SUSPENDED: {
                if (frame->limit <= 0) {
                    frame->state = STATE_DONE;
                    return false;
                }

                frame->current_value = frame->b;
                int next = frame->a + frame->b;
                frame->a = frame->b;
                frame->b = next;
                frame->limit--;
                return true;
            }

            case STATE_DONE:
                return false;
        }

        return false;
    }

    int value() const {
        return frame->current_value;
    }
};

// ============================================================================
// Range Generator (with step)
// ============================================================================

struct RangeFrame {
    CoroutineState state;
    int start, end, step;
    int current;
};

struct Range {
    RangeFrame* frame;

    Range(int start, int end, int step = 1) {
        frame = (RangeFrame*)malloc(sizeof(RangeFrame));
        frame->state = STATE_START;
        frame->start = start;
        frame->end = end;
        frame->step = step;
        frame->current = start;
    }

    ~Range() {
        if (frame) {
            free(frame);
        }
    }

    bool next() {
        if (frame->state == STATE_DONE) {
            return false;
        }

        switch (frame->state) {
            case STATE_START:
                frame->current = frame->start;
                if (frame->current < frame->end) {
                    frame->state = STATE_SUSPENDED;
                    return true;
                } else {
                    frame->state = STATE_DONE;
                    return false;
                }

            case STATE_SUSPENDED:
                frame->current += frame->step;
                if (frame->current < frame->end) {
                    return true;
                } else {
                    frame->state = STATE_DONE;
                    return false;
                }

            case STATE_DONE:
                return false;
        }

        return false;
    }

    int value() const {
        return frame->current;
    }
};

// ============================================================================
// Filter Generator (composable)
// ============================================================================

template<typename Generator, typename Predicate>
struct Filter {
    Generator* source;
    Predicate pred;
    bool owns_source;

    Filter(Generator* gen, Predicate p, bool owns = false)
        : source(gen), pred(p), owns_source(owns) {}

    ~Filter() {
        if (owns_source && source) {
            delete source;
        }
    }

    bool next() {
        while (source->next()) {
            if (pred(source->value())) {
                return true;
            }
        }
        return false;
    }

    int value() const {
        return source->value();
    }
};

// ============================================================================
// Map Generator (composable)
// ============================================================================

template<typename Generator, typename Function>
struct Map {
    Generator* source;
    Function func;
    int mapped_value;
    bool owns_source;

    Map(Generator* gen, Function f, bool owns = false)
        : source(gen), func(f), mapped_value(0), owns_source(owns) {}

    ~Map() {
        if (owns_source && source) {
            delete source;
        }
    }

    bool next() {
        if (source->next()) {
            mapped_value = func(source->value());
            return true;
        }
        return false;
    }

    int value() const {
        return mapped_value;
    }
};

// ============================================================================
// Examples
// ============================================================================

void example1_simple_counter() {
    printf("\n=== Example 1: Simple Counter ===\n");

    Counter gen(5);
    while (gen.next()) {
        printf("%d ", gen.value());
    }
    printf("\n");
}

void example2_fibonacci() {
    printf("\n=== Example 2: Fibonacci Sequence ===\n");

    Fibonacci gen(10);
    while (gen.next()) {
        printf("%d ", gen.value());
    }
    printf("\n");
}

void example3_range() {
    printf("\n=== Example 3: Range Generator ===\n");

    printf("Range(10, 20, step=2): ");
    Range gen(10, 20, 2);
    while (gen.next()) {
        printf("%d ", gen.value());
    }
    printf("\n");
}

void example4_filter() {
    printf("\n=== Example 4: Filter Generator ===\n");

    printf("Even numbers from 1-20: ");
    Range* range = new Range(1, 21);
    Filter<Range, bool(*)(int)> gen(range, [](int x) { return x % 2 == 0; }, true);

    while (gen.next()) {
        printf("%d ", gen.value());
    }
    printf("\n");
}

void example5_map() {
    printf("\n=== Example 5: Map Generator ===\n");

    printf("Squares: ");
    Range* range = new Range(0, 10);
    Map<Range, int(*)(int)> gen(range, [](int x) { return x * x; }, true);

    while (gen.next()) {
        printf("%d ", gen.value());
    }
    printf("\n");
}

// ============================================================================
// Main
// ============================================================================

int main() {
    printf("Coroutine Generator Example\n");
    printf("===========================\n");

    example1_simple_counter();
    example2_fibonacci();
    example3_range();
    example4_filter();
    example5_map();

    printf("\n=== All examples completed ===\n");

    return 0;
}
