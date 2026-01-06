/**
 * C++ Standard Library Header Provider
 * Maps C++ standard library headers to C equivalents for transpilation
 */

import { HeaderProvider } from '../types.js';
import { CStandardLibraryProvider } from './stdlib-provider.js';

/**
 * C++ Standard Library to C Standard Library mapping
 * Maps C++ headers to their C equivalents where possible
 */
export class CppStandardLibraryProvider implements HeaderProvider {
    private cStdlibProvider: CStandardLibraryProvider;

    /**
     * Maps C++ headers to C equivalents
     * null means the header is not supported (requires transpilation of complex C++ features)
     */
    private mappings = new Map<string, string | null>([
        // I/O Stream → stdio.h
        ['iostream', 'stdio.h'],
        ['fstream', 'stdio.h'],
        ['sstream', null], // Not directly mappable

        // C++ wrappers for C headers (remove .h, add c prefix)
        ['cstdio', 'stdio.h'],
        ['cstdlib', 'stdlib.h'],
        ['cstring', 'string.h'],
        ['cmath', 'math.h'],
        ['cassert', 'assert.h'],
        ['cstddef', 'stddef.h'],
        ['cstdarg', 'stdarg.h'],

        // Container headers (not directly mappable to C)
        ['vector', null],
        ['list', null],
        ['deque', null],
        ['map', null],
        ['set', null],
        ['unordered_map', null],
        ['unordered_set', null],
        ['array', null],
        ['queue', null],
        ['stack', null],

        // String (C++ std::string → C char*)
        ['string', null], // Requires transpilation

        // Algorithm (some functions mappable, others not)
        ['algorithm', null],

        // Memory management
        ['memory', null], // smart pointers not in C

        // Utilities
        ['utility', null],
        ['functional', null],
        ['iterator', null],

        // Exception handling (not in C)
        ['exception', null],
        ['stdexcept', null],

        // Type support
        ['type_traits', null],
        ['typeinfo', null],

        // Limits
        ['limits', null],

        // Numeric
        ['numeric', null],
        ['complex', null],

        // Time
        ['ctime', null],
        ['chrono', null],

        // Thread (not in C89-C11)
        ['thread', null],
        ['mutex', null],
        ['condition_variable', null],
        ['atomic', null],
    ]);

    constructor() {
        this.cStdlibProvider = new CStandardLibraryProvider();
    }

    getHeader(name: string): string | null {
        // Check if we have a mapping for this C++ header
        if (this.mappings.has(name)) {
            const mapped = this.mappings.get(name);
            if (mapped) {
                // Return the C equivalent header content
                return this.cStdlibProvider.getHeader(mapped);
            }
            // null means this header is not supported
            return null;
        }

        // If no mapping exists, try to get it directly from C stdlib
        // (handles cases where C++ code includes C headers directly)
        return this.cStdlibProvider.getHeader(name);
    }

    hasHeader(name: string): boolean {
        if (this.mappings.has(name)) {
            const mapped = this.mappings.get(name);
            if (mapped === null || mapped === undefined) {
                return false;
            }
            return this.cStdlibProvider.hasHeader(mapped);
        }
        return this.cStdlibProvider.hasHeader(name);
    }

    listHeaders(): string[] {
        // Return all C++ headers that can be mapped to C
        const supported: string[] = [];
        for (const [cppHeader, cHeader] of this.mappings.entries()) {
            if (cHeader !== null) {
                supported.push(cppHeader);
            }
        }
        // Also include direct C headers
        return [...supported, ...this.cStdlibProvider.listHeaders()];
    }

    /**
     * Check if a C++ header is supported (has a C equivalent)
     */
    isSupported(name: string): boolean {
        return this.hasHeader(name);
    }

    /**
     * Get the C equivalent header name for a C++ header
     */
    getMappedHeaderName(cppHeaderName: string): string | null {
        return this.mappings.get(cppHeaderName) || null;
    }

    /**
     * List all C++ headers that are NOT supported
     */
    listUnsupportedHeaders(): string[] {
        const unsupported: string[] = [];
        for (const [cppHeader, cHeader] of this.mappings.entries()) {
            if (cHeader === null) {
                unsupported.push(cppHeader);
            }
        }
        return unsupported;
    }
}
