/**
 * TypeScript types for C++ to C transpilation API
 *
 * These types correspond to the C++ structures defined in TranspilerAPI.h
 * SOLID Principles:
 * - Interface Segregation: Clean separation of concerns
 * - Dependency Inversion: API depends on these abstractions
 */

/**
 * ACSL annotation configuration
 * Maps to TranspileOptions::ACSLConfig in TranspilerAPI.h
 */
export interface ACSLConfig {
  /** Generate statement-level ACSL annotations */
  statements?: boolean;
  /** Generate type invariant annotations */
  typeInvariants?: boolean;
  /** Generate axiomatic definitions */
  axiomatics?: boolean;
  /** Generate ghost code for verification */
  ghostCode?: boolean;
  /** Generate behavior specifications */
  behaviors?: boolean;
  /** Generate memory predicates (allocable, freeable, etc.) */
  memoryPredicates?: boolean;
}

/**
 * ACSL coverage level
 * Maps to TranspileOptions::ACSLLevelEnum
 */
export type ACSLLevel = 'basic' | 'full';

/**
 * ACSL output mode
 * Maps to TranspileOptions::ACSLOutputModeEnum
 */
export type ACSLOutputMode = 'inline' | 'separate';

/**
 * Target C standard
 */
export type CStandard = 'c89' | 'c99' | 'c11' | 'c17';

/**
 * Exception handling model
 */
export type ExceptionModel = 'sjlj' | 'tables';

/**
 * Transpilation options
 * Maps to cpptoc::TranspileOptions in TranspilerAPI.h
 */
export interface TranspileOptions {
  /** ACSL annotation configuration */
  acsl?: ACSLConfig;

  /** ACSL coverage level (requires acsl options enabled) */
  acslLevel?: ACSLLevel;

  /** ACSL output mode (requires acsl options enabled) */
  acslOutputMode?: ACSLOutputMode;

  /** Target C standard (default: c99) */
  target?: CStandard;

  /** C++ standard version (11, 14, 17, 20, 23) */
  cppStandard?: number;

  /** Enable optimization passes */
  optimize?: boolean;

  /** Enable template monomorphization (Phase 11) */
  monomorphizeTemplates?: boolean;

  /** Maximum template instantiations (Phase 11) */
  templateInstantiationLimit?: number;

  /** Enable exception handling translation (Phase 12) */
  enableExceptions?: boolean;

  /** Exception handling model (Phase 12) */
  exceptionModel?: ExceptionModel;

  /** Enable RTTI translation (Phase 13) */
  enableRTTI?: boolean;

  /** Use #pragma once instead of include guards */
  usePragmaOnce?: boolean;

  /** Generate dependency graph in DOT format */
  generateDependencyGraph?: boolean;
}

/**
 * Diagnostic message severity levels
 */
export type DiagnosticSeverity = 'error' | 'warning' | 'note';

/**
 * Diagnostic message from transpilation
 * Maps to cpptoc::Diagnostic in TranspilerAPI.h
 */
export interface Diagnostic {
  /** Source line number (0 if not applicable) */
  line: number;

  /** Source column number (0 if not applicable) */
  column: number;

  /** Diagnostic message text */
  message: string;

  /** Severity level */
  severity: DiagnosticSeverity;
}

/**
 * Result of transpilation operation
 * Maps to cpptoc::TranspileResult in TranspilerAPI.h
 */
export interface TranspileResult {
  /** True if transpilation succeeded */
  success: boolean;

  /** Generated C implementation code (.c file) */
  c: string;

  /** Generated C header code (.h file) */
  h: string;

  /** ACSL annotations (if separate mode enabled) */
  acsl: string;

  /** DOT dependency graph (if requested) */
  dependencyGraph?: string;

  /** All diagnostic messages (errors, warnings, notes) */
  diagnostics: Diagnostic[];
}

/**
 * API request body for /transpile endpoint
 */
export interface TranspileRequest {
  /** C++ source code to transpile */
  cpp: string;

  /** Source filename (for error messages and #line directives) */
  filename?: string;

  /** Transpilation configuration options */
  options?: TranspileOptions;
}

/**
 * API response for /transpile endpoint
 * Extends TranspileResult with additional metadata
 */
export interface TranspileResponse extends TranspileResult {
  /** Processing time in milliseconds */
  processingTime?: number;

  /** API version */
  version?: string;
}

/**
 * Error response
 */
export interface ErrorResponse {
  /** Error flag */
  success: false;

  /** Error message */
  error: string;

  /** HTTP status code */
  statusCode: number;

  /** Optional validation errors */
  validationErrors?: Array<{
    field: string;
    message: string;
  }>;
}
