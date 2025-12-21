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

export interface TranspileOptions {
    acsl?: ACSLOptions;
    target?: 'c89' | 'c99' | 'c11' | 'c17';
    optimize?: boolean;
}

export interface TranspileResult {
    success: boolean;
    c: string;
    acsl: string;
    diagnostics: Diagnostic[];
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
