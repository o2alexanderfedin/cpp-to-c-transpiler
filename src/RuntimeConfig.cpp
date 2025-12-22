// RuntimeConfig.cpp - Global runtime configuration accessors for tests
//
// This file provides default implementations of runtime configuration functions
// that are normally defined in main.cpp. Tests link against this file instead
// of main.cpp to avoid multiple main() definitions.
//
// Phase 15: Test Migration to GTest - v3.0.0

#include "ACSLGenerator.h"
#include <string>

// Default configuration values for tests
static bool g_generateACSL = false;
static ACSLLevel g_acslLevel = ACSLLevel::Basic;
static ACSLOutputMode g_acslOutputMode = ACSLOutputMode::Inline;
static bool g_generateMemoryPredicates = false;
static bool g_monomorphizeTemplates = false;
static unsigned int g_templateInstantiationLimit = 100;
static bool g_enableExceptions = false;
static bool g_enableRTTI = false;

// Global accessor for ACSL generation setting
bool shouldGenerateACSL() {
  return g_generateACSL;
}

// Global accessor for ACSL level
ACSLLevel getACSLLevel() {
  return g_acslLevel;
}

// Global accessor for ACSL output mode
ACSLOutputMode getACSLOutputMode() {
  return g_acslOutputMode;
}

// Global accessor for ACSL memory predicates setting (Phase 6, v1.23.0)
bool shouldGenerateMemoryPredicates() {
  return g_generateMemoryPredicates;
}

// Global accessor for template monomorphization setting (Phase 11, v2.4.0)
bool shouldMonomorphizeTemplates() {
  return g_monomorphizeTemplates;
}

// Global accessor for template instantiation limit (Phase 11, v2.4.0)
unsigned int getTemplateInstantiationLimit() {
  return g_templateInstantiationLimit;
}

// Global accessor for exception handling setting (Phase 12, v2.5.0)
bool shouldEnableExceptions() {
  return g_enableExceptions;
}

// Global accessor for exception model (Phase 12, v2.5.0)
std::string getExceptionModel() {
  return "sjlj";  // Default to setjmp/longjmp for tests
}

// Global accessor for RTTI setting (Phase 13, v2.6.0)
bool shouldEnableRTTI() {
  return g_enableRTTI;
}

// Test helper functions to set configuration values
void setGenerateACSL(bool value) { g_generateACSL = value; }
void setACSLLevel(ACSLLevel level) { g_acslLevel = level; }
void setACSLOutputMode(ACSLOutputMode mode) { g_acslOutputMode = mode; }
void setGenerateMemoryPredicates(bool value) { g_generateMemoryPredicates = value; }
void setMonomorphizeTemplates(bool value) { g_monomorphizeTemplates = value; }
void setTemplateInstantiationLimit(unsigned int limit) { g_templateInstantiationLimit = limit; }
void setEnableExceptions(bool value) { g_enableExceptions = value; }
void setEnableRTTI(bool value) { g_enableRTTI = value; }
