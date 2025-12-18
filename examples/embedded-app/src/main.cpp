// Embedded Temperature Monitor Example
// Demonstrates C++ to C transpiler for embedded systems

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

// Hardware register definitions (simulated for testing)
#ifdef NATIVE_BUILD
    // Simulated hardware for native testing
    static uint32_t sim_gpio_port = 0;
    static uint32_t sim_adc_value = 68;
    static uint32_t sim_uart_buffer[256];
    static size_t sim_uart_idx = 0;

    #define GPIO_BASE ((volatile uint32_t*)&sim_gpio_port)
    #define ADC_BASE ((volatile uint32_t*)&sim_adc_value)
    #define UART_BASE ((volatile uint32_t*)sim_uart_buffer)
#else
    // Real hardware addresses (ARM Cortex-M)
    #define GPIO_BASE ((volatile uint32_t*)0x40020000)
    #define ADC_BASE ((volatile uint32_t*)0x40012000)
    #define UART_BASE ((volatile uint32_t*)0x40011000)
#endif

// Constants
constexpr uint32_t TEMP_THRESHOLD_HIGH = 75;
constexpr uint32_t TEMP_THRESHOLD_LOW = 70;
constexpr uint32_t ADC_MAX = 4095;
constexpr uint32_t TEMP_MAX = 125;

// ============================================================================
// GPIO Abstraction
// ============================================================================

class GPIO {
    volatile uint32_t* port;
    uint32_t pin_mask;

public:
    GPIO(volatile uint32_t* port_addr, uint32_t pin)
        : port(port_addr), pin_mask(1u << pin) {
    }

    inline void setHigh() {
        *port |= pin_mask;
    }

    inline void setLow() {
        *port &= ~pin_mask;
    }

    inline bool read() const {
        return (*port & pin_mask) != 0;
    }

    inline void toggle() {
        *port ^= pin_mask;
    }
};

// ============================================================================
// ADC Abstraction
// ============================================================================

class ADC {
    volatile uint32_t* adc_reg;

public:
    ADC(volatile uint32_t* adc_addr) : adc_reg(adc_addr) {
    }

    uint32_t read() const {
#ifdef NATIVE_BUILD
        // Simulate ADC reading
        return *adc_reg;
#else
        // Trigger conversion
        *adc_reg |= (1u << 0);
        // Wait for conversion complete
        while ((*adc_reg & (1u << 1)) == 0) {}
        // Read result
        return (*adc_reg >> 16) & 0xFFF;
#endif
    }

    void setChannel(uint32_t channel) {
        *adc_reg = (*adc_reg & ~0xF0) | ((channel & 0xF) << 4);
    }
};

// ============================================================================
// UART Abstraction
// ============================================================================

class UART {
    volatile uint32_t* uart_reg;

public:
    UART(volatile uint32_t* uart_addr) : uart_reg(uart_addr) {
    }

    void write(char c) {
#ifdef NATIVE_BUILD
        if (sim_uart_idx < 256) {
            sim_uart_buffer[sim_uart_idx++] = c;
        }
#else
        // Wait for transmit buffer empty
        while ((*uart_reg & (1u << 7)) == 0) {}
        *uart_reg = c;
#endif
    }

    void write(const char* str) {
        while (*str) {
            write(*str++);
        }
    }

    void writeInt(int value) {
        if (value < 0) {
            write('-');
            value = -value;
        }

        char buffer[12];
        int i = 0;
        do {
            buffer[i++] = '0' + (value % 10);
            value /= 10;
        } while (value > 0);

        // Reverse and print
        while (i > 0) {
            write(buffer[--i]);
        }
    }
};

// ============================================================================
// Temperature Sensor
// ============================================================================

class TemperatureSensor {
    ADC& adc;
    uint32_t channel;

public:
    TemperatureSensor(ADC& adc_ref, uint32_t adc_channel)
        : adc(adc_ref), channel(adc_channel) {
        adc.setChannel(channel);
    }

    int readCelsius() const {
        uint32_t raw = adc.read();
        // Convert ADC reading to temperature (linear approximation)
        return (raw * TEMP_MAX) / ADC_MAX;
    }
};

// ============================================================================
// Fan Controller
// ============================================================================

class FanController {
    GPIO& fan_gpio;
    bool is_on;

public:
    FanController(GPIO& gpio) : fan_gpio(gpio), is_on(false) {
        fan_gpio.setLow();
    }

    ~FanController() {
        // Ensure fan is off on destruction
        turnOff();
    }

    void turnOn() {
        if (!is_on) {
            fan_gpio.setHigh();
            is_on = true;
        }
    }

    void turnOff() {
        if (is_on) {
            fan_gpio.setLow();
            is_on = false;
        }
    }

    bool isOn() const { return is_on; }
};

// ============================================================================
// Critical Section (RAII for interrupt disable)
// ============================================================================

#ifndef NATIVE_BUILD
static inline uint32_t disable_interrupts() {
    uint32_t primask;
    __asm__ volatile ("mrs %0, primask" : "=r" (primask));
    __asm__ volatile ("cpsid i" ::: "memory");
    return primask;
}

static inline void restore_interrupts(uint32_t primask) {
    __asm__ volatile ("msr primask, %0" :: "r" (primask) : "memory");
}
#else
static inline uint32_t disable_interrupts() { return 0; }
static inline void restore_interrupts(uint32_t) {}
#endif

class CriticalSection {
    uint32_t prev_state;

public:
    CriticalSection() : prev_state(disable_interrupts()) {}

    ~CriticalSection() {
        restore_interrupts(prev_state);
    }

    // Non-copyable
    CriticalSection(const CriticalSection&) = delete;
    CriticalSection& operator=(const CriticalSection&) = delete;
};

// ============================================================================
// Temperature Monitor System
// ============================================================================

class TemperatureMonitor {
    TemperatureSensor& sensor;
    FanController& fan;
    UART& uart;
    int last_temp;
    bool fan_active;

public:
    TemperatureMonitor(TemperatureSensor& temp_sensor,
                       FanController& fan_ctrl,
                       UART& uart_ref)
        : sensor(temp_sensor), fan(fan_ctrl), uart(uart_ref),
          last_temp(0), fan_active(false) {
    }

    void update(uint32_t time_seconds) {
        int current_temp = sensor.readCelsius();

        // Update display
        uart.write("[");
        uart.writeInt(time_seconds);
        uart.write("s] Temperature: ");
        uart.writeInt(current_temp);
        uart.write("C - ");

        // Control fan based on temperature
        if (current_temp >= TEMP_THRESHOLD_HIGH && !fan_active) {
            fan.turnOn();
            fan_active = true;
            uart.write("HIGH! Fan ON\n");
        } else if (current_temp <= TEMP_THRESHOLD_LOW && fan_active) {
            fan.turnOff();
            fan_active = false;
            uart.write("Normal, Fan OFF\n");
        } else if (fan_active) {
            uart.write("Cooling...\n");
        } else {
            uart.write("Normal\n");
        }

        last_temp = current_temp;
    }

    int getLastTemperature() const { return last_temp; }
    bool isFanActive() const { return fan_active; }
};

// ============================================================================
// Test Functions
// ============================================================================

#ifdef NATIVE_BUILD
void simulateTemperatureRise() {
    // Simulate temperature rising over time
    static int sim_temp = 68;
    static int direction = 1;

    sim_temp += direction * 2;
    if (sim_temp >= 80) direction = -1;
    if (sim_temp <= 68) direction = 1;

    sim_adc_value = (sim_temp * ADC_MAX) / TEMP_MAX;
}

void testCriticalSection(UART& uart) {
    uart.write("\nCritical section test: ");

    uint32_t counter = 0;
    {
        CriticalSection cs;
        counter++;
        // Interrupts disabled here
        counter++;
    }
    // Interrupts restored here

    if (counter == 2) {
        uart.write("PASSED\n");
    } else {
        uart.write("FAILED\n");
    }
}

void testGPIO(GPIO& gpio, UART& uart) {
    uart.write("GPIO test: ");

    gpio.setHigh();
    if (!gpio.read()) {
        uart.write("FAILED (set high)\n");
        return;
    }

    gpio.setLow();
    if (gpio.read()) {
        uart.write("FAILED (set low)\n");
        return;
    }

    uart.write("PASSED\n");
}
#endif

// ============================================================================
// Main Application
// ============================================================================

int main() {
    // Initialize hardware peripherals
    GPIO fan_pin(GPIO_BASE, 0);
    ADC adc(ADC_BASE);
    UART uart(UART_BASE);

    uart.write("Embedded Temperature Monitor\n");
    uart.write("============================\n");
    uart.write("Initializing hardware...\n");

#ifdef NATIVE_BUILD
    uart.write("  GPIO initialized: 0x40020000\n");
    uart.write("  ADC initialized: 0x40012000\n");
    uart.write("  UART initialized: 0x40011000\n");
#endif

    // Initialize subsystems
    TemperatureSensor temp_sensor(adc, 0);
    FanController fan(fan_pin);
    TemperatureMonitor monitor(temp_sensor, fan, uart);

    uart.write("\nStarting temperature monitoring...\n");

    // Main monitoring loop
#ifdef NATIVE_BUILD
    // Run simulation for testing
    for (uint32_t t = 0; t < 6; t++) {
        monitor.update(t);
        simulateTemperatureRise();
    }

    // Run tests
    testCriticalSection(uart);
    testGPIO(fan_pin, uart);

    uart.write("\nSystem running normally.\n");
#else
    // Embedded: infinite monitoring loop
    uint32_t time = 0;
    while (true) {
        monitor.update(time++);

        // Delay 1 second (assume system tick is configured)
        for (volatile uint32_t i = 0; i < 7200000; i++) {}
    }
#endif

    return 0;
}
