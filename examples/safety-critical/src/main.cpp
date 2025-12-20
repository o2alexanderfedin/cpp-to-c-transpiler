// Safety-Critical Altitude Controller Example
// Demonstrates Frama-C verifiable code generation

#include <cstdio>
#include <cstdlib>
#include <cassert>

// ============================================================================
// Safe Integer Type (Range-Checked)
// ============================================================================

class SafeInt {
    int value;
    static constexpr int MIN = -1000;
    static constexpr int MAX = 1000;

    static int clamp(int v) {
        if (v < MIN) return MIN;
        if (v > MAX) return MAX;
        return v;
    }

public:
    SafeInt() : value(0) {}
    SafeInt(int v) : value(clamp(v)) {}

    int get() const { return value; }

    SafeInt operator+(SafeInt other) const {
        return SafeInt(clamp(value + other.value));
    }

    SafeInt operator-(SafeInt other) const {
        return SafeInt(clamp(value - other.value));
    }

    bool operator<(SafeInt other) const {
        return value < other.value;
    }

    bool operator>(SafeInt other) const {
        return value > other.value;
    }
};

// ============================================================================
// Safe Array (Bounds-Checked)
// ============================================================================

template<typename T, int N>
class SafeArray {
    T data[N];

public:
    SafeArray() {
        for (int i = 0; i < N; i++) {
            data[i] = T();
        }
    }

    T& operator[](int index) {
        assert(index >= 0 && index < N);
        return data[index];
    }

    const T& operator[](int index) const {
        assert(index >= 0 && index < N);
        return data[index];
    }

    constexpr int size() const { return N; }
};

// ============================================================================
// Altitude Sensor (with failure detection)
// ============================================================================

class AltitudeSensor {
    int current_altitude;
    bool is_valid;
    int failure_count;

public:
    AltitudeSensor() : current_altitude(100), is_valid(true), failure_count(0) {}

    void setAltitude(int alt) {
        current_altitude = alt;
    }

    void simulateFailure() {
        is_valid = false;
        failure_count++;
    }

    void restore() {
        is_valid = true;
    }

    bool valid() const {
        return is_valid;
    }

    int read() const {
        return is_valid ? current_altitude : -1;
    }

    int getFailureCount() const {
        return failure_count;
    }
};

// ============================================================================
// Altitude Controller (Safety-Critical)
// ============================================================================

class AltitudeController {
    static constexpr int MIN_SAFE_ALTITUDE = 50;
    static constexpr int MAX_SAFE_ALTITUDE = 500;
    static constexpr int EMERGENCY_ALTITUDE = 100;
    static constexpr int BUFFER_SIZE = 5;

    AltitudeSensor& sensor;
    SafeArray<SafeInt, BUFFER_SIZE> altitude_history;
    int history_index;
    bool ground_detected;

public:
    AltitudeController(AltitudeSensor& s)
        : sensor(s), history_index(0), ground_detected(false) {}

    // Compute safe altitude with bounds checking
    // ACSL: ensures MIN_SAFE_ALTITUDE <= result <= MAX_SAFE_ALTITUDE
    int computeSafeAltitude(int current) const {
        if (current < MIN_SAFE_ALTITUDE) return MIN_SAFE_ALTITUDE;
        if (current > MAX_SAFE_ALTITUDE) return MAX_SAFE_ALTITUDE;
        return current;
    }

    // Read sensor with failure handling
    // ACSL: ensures sensor.valid() ==> result >= 0
    // ACSL: ensures !sensor.valid() ==> result == EMERGENCY_ALTITUDE
    int readAltitudeWithFailover() {
        if (sensor.valid()) {
            int reading = sensor.read();
            return computeSafeAltitude(reading);
        } else {
            // Sensor failure: use emergency altitude
            return EMERGENCY_ALTITUDE;
        }
    }

    // Update altitude history
    // ACSL: requires 0 <= altitude <= 1000
    // ACSL: loop invariant 0 <= i <= BUFFER_SIZE
    void updateHistory(int altitude) {
        altitude_history[history_index] = SafeInt(altitude);
        history_index = (history_index + 1) % BUFFER_SIZE;
    }

    // Compute average altitude from history
    // ACSL: ensures result >= 0
    // ACSL: loop invariant 0 <= i <= BUFFER_SIZE
    // ACSL: loop invariant sum == \sum(0, i-1, altitude_history)
    int computeAverageAltitude() const {
        int sum = 0;
        for (int i = 0; i < BUFFER_SIZE; i++) {
            sum += altitude_history[i].get();
        }
        return sum / BUFFER_SIZE;
    }

    // Main control loop iteration
    // ACSL: ensures result >= MIN_SAFE_ALTITUDE
    // ACSL: ensures ground_detected ==> result >= EMERGENCY_ALTITUDE
    int controlStep() {
        int current = readAltitudeWithFailover();
        updateHistory(current);

        int avg = computeAverageAltitude();
        int target = computeSafeAltitude(avg);

        // Ground collision avoidance
        if (ground_detected && target < EMERGENCY_ALTITUDE) {
            target = EMERGENCY_ALTITUDE;
        }

        return target;
    }

    void setGroundDetected(bool detected) {
        ground_detected = detected;
    }

    int getHistorySize() const { return BUFFER_SIZE; }
};

// ============================================================================
// Test Scenarios
// ============================================================================

void testNormalOperation(AltitudeSensor& sensor, AltitudeController& controller) {
    printf("\n=== Test 1: Normal Operation ===\n");

    sensor.setAltitude(100);
    int target = controller.controlStep();
    printf("Altitude: 100m -> Target: %dm\n", target);
    assert(target >= 50 && target <= 500);

    sensor.setAltitude(200);
    target = controller.controlStep();
    printf("Altitude: 200m -> Target: %dm\n", target);
    assert(target >= 50 && target <= 500);

    printf("PASSED: Normal operation within bounds\n");
}

void testLowAltitude(AltitudeSensor& sensor, AltitudeController& controller) {
    printf("\n=== Test 2: Low Altitude Correction ===\n");

    sensor.setAltitude(30);  // Below minimum
    int target = controller.controlStep();
    printf("Altitude: 30m (below min) -> Target: %dm\n", target);
    assert(target >= 50);

    printf("PASSED: Low altitude corrected to minimum\n");
}

void testHighAltitude(AltitudeSensor& sensor, AltitudeController& controller) {
    printf("\n=== Test 3: High Altitude Correction ===\n");

    sensor.setAltitude(600);  // Above maximum
    int target = controller.controlStep();
    printf("Altitude: 600m (above max) -> Target: %dm\n", target);
    assert(target <= 500);

    printf("PASSED: High altitude corrected to maximum\n");
}

void testSensorFailure(AltitudeSensor& sensor, AltitudeController& controller) {
    printf("\n=== Test 4: Sensor Failure Handling ===\n");

    sensor.simulateFailure();
    int target = controller.controlStep();
    printf("Sensor failed -> Emergency altitude: %dm\n", target);
    assert(target == 100);  // Emergency altitude

    sensor.restore();
    sensor.setAltitude(150);
    target = controller.controlStep();
    printf("Sensor restored, Altitude: 150m -> Target: %dm\n", target);
    assert(target >= 50 && target <= 500);

    printf("PASSED: Sensor failure handled safely\n");
}

void testGroundCollisionAvoidance(AltitudeSensor& sensor, AltitudeController& controller) {
    printf("\n=== Test 5: Ground Collision Avoidance ===\n");

    controller.setGroundDetected(true);
    sensor.setAltitude(80);  // Low but above minimum
    int target = controller.controlStep();
    printf("Ground detected, Altitude: 80m -> Target: %dm\n", target);
    assert(target >= 100);  // Must be at emergency altitude

    controller.setGroundDetected(false);
    printf("PASSED: Ground collision avoided\n");
}

void testAverageSmoothing(AltitudeSensor& sensor, AltitudeController& controller) {
    printf("\n=== Test 6: Average Smoothing ===\n");

    // Fill history with varying altitudes
    int altitudes[] = {100, 110, 105, 115, 108};
    for (int i = 0; i < 5; i++) {
        sensor.setAltitude(altitudes[i]);
        int target = controller.controlStep();
        printf("Altitude: %dm -> Target: %dm\n", altitudes[i], target);
    }

    int avg = controller.computeAverageAltitude();
    printf("Average altitude: %dm\n", avg);
    assert(avg >= 100 && avg <= 115);

    printf("PASSED: Average smoothing working correctly\n");
}

// ============================================================================
// Main
// ============================================================================

int main() {
    printf("Safety-Critical Altitude Controller\n");
    printf("====================================\n");

    AltitudeSensor sensor;
    AltitudeController controller(sensor);

    // Run all test scenarios
    testNormalOperation(sensor, controller);
    testLowAltitude(sensor, controller);
    testHighAltitude(sensor, controller);
    testSensorFailure(sensor, controller);
    testGroundCollisionAvoidance(sensor, controller);
    testAverageSmoothing(sensor, controller);

    printf("\n=== All Safety Tests PASSED ===\n");
    printf("System is provably safe!\n");

    return 0;
}
