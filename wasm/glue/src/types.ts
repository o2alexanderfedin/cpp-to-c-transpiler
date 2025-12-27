/**
 * TypeScript types for cpptoc WASM API
 * Auto-generated types from embind are augmented here
 */

export interface Diagnostic {
    line: number;
    column: number;
    message: string;
    severity: 'error' | 'warning' | 'note';
}

export interface ACSLOptions {
    statements?: boolean;
    typeInvariants?: boolean;
    axiomatics?: boolean;
    ghostCode?: boolean;
    behaviors?: boolean;
}

/**
 * Header provider interface for resolving #include directives
 * Enables on-demand header loading in WebAssembly scenario
 */
export interface HeaderProvider {
    /**
     * Get header content by name
     * @param headerName - e.g., "stdio.h", "vector", "custom/myheader.h"
     * @returns Header content as string, or null if not found
     */
    getHeader(headerName: string): string | null;

    /**
     * Check if header exists
     */
    hasHeader(headerName: string): boolean;

    /**
     * List all available headers
     */
    listHeaders(): string[];
}

export interface TranspileOptions {
    acsl?: ACSLOptions;
    target?: 'c89' | 'c99' | 'c11' | 'c17';
    optimize?: boolean;
    /**
     * Header provider for resolving #include directives
     * Required for transpiling code that includes headers
     */
    headerProvider?: HeaderProvider;
    /**
     * C++ standard version (11, 14, 17, 20)
     */
    cppStandard?: 11 | 14 | 17 | 20;
    /**
     * Enable ACSL annotation generation
     */
    enableACSL?: boolean;
    /**
     * ACSL annotation level (1-5)
     */
    acslLevel?: 1 | 2 | 3 | 4 | 5;
}

export interface TranspileResult {
    success: boolean;
    c: string;
    /**
     * Header file (.h) - Phase 28
     * Contains forward declarations, struct definitions, and function signatures
     */
    h: string;
    acsl: string;
    diagnostics: Diagnostic[];
    /**
     * Required headers not found by header provider
     */
    missingHeaders?: string[];
    /**
     * Header files generated or used (name → content)
     */
    headers?: Map<string, string>;
}

export interface WASMModule {
    Transpiler: new () => TranspilerInstance;
}

export interface TranspilerInstance {
    transpile(code: string, options: TranspileOptions): TranspileResult;
    getVersion(): string;
    delete(): void;
}

export interface CreateModuleOptions {
    locateFile?: (path: string, prefix: string) => string;
    onRuntimeInitialized?: () => void;
}

export type CreateCppToCModule = (options?: CreateModuleOptions) => Promise<WASMModule>;

/**
 * Default ACSL options for common use cases
 */
export const DEFAULT_ACSL_OPTIONS: ACSLOptions = {
    statements: true,
    typeInvariants: true,
    axiomatics: false,
    ghostCode: false,
    behaviors: true
};

/**
 * Default transpile options
 */
export const DEFAULT_TRANSPILE_OPTIONS: TranspileOptions = {
    acsl: DEFAULT_ACSL_OPTIONS,
    target: 'c99',
    optimize: false
};

/**
 * Type guard for checking if result has errors
 */
export function hasErrors(result: TranspileResult): boolean {
    return !result.success || result.diagnostics.some(d => d.severity === 'error');
}

/**
 * Get only error diagnostics
 */
export function getErrors(result: TranspileResult): Diagnostic[] {
    return result.diagnostics.filter(d => d.severity === 'error');
}

/**
 * Get only warning diagnostics
 */
export function getWarnings(result: TranspileResult): Diagnostic[] {
    return result.diagnostics.filter(d => d.severity === 'warning');
}

/**
 * Format diagnostic message for display
 */
export function formatDiagnostic(diagnostic: Diagnostic): string {
    const location = diagnostic.line > 0
        ? `${diagnostic.line}:${diagnostic.column}`
        : 'global';
    return `[${diagnostic.severity.toUpperCase()}] ${location}: ${diagnostic.message}`;
}
