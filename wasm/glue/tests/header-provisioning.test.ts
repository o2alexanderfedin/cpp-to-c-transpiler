/**
 * Header Provisioning Tests
 * Tests the header provider API design and functionality
 *
 * Note: These tests verify the API design and header provisioning logic.
 * Actual WASM transpilation integration is future work (not in this phase).
 */

import { describe, it, expect } from 'vitest';
import { CStandardLibraryProvider } from '../src/headers/stdlib-provider';
import { CppStandardLibraryProvider } from '../src/headers/cpp-stdlib-provider';
import type { HeaderProvider } from '../src/types';

describe('Header Provisioning API', () => {
    describe('CStandardLibraryProvider', () => {
        it('should provide stdio.h header', () => {
            const provider = new CStandardLibraryProvider();
            const header = provider.getHeader('stdio.h');

            expect(header).not.toBeNull();
            expect(header).toContain('printf');
            expect(header).toContain('fprintf');
            expect(header).toContain('FILE');
        });

        it('should provide stdlib.h header', () => {
            const provider = new CStandardLibraryProvider();
            const header = provider.getHeader('stdlib.h');

            expect(header).not.toBeNull();
            expect(header).toContain('malloc');
            expect(header).toContain('free');
            expect(header).toContain('exit');
        });

        it('should provide string.h header', () => {
            const provider = new CStandardLibraryProvider();
            const header = provider.getHeader('string.h');

            expect(header).not.toBeNull();
            expect(header).toContain('strcpy');
            expect(header).toContain('strlen');
            expect(header).toContain('memcpy');
        });

        it('should provide math.h header', () => {
            const provider = new CStandardLibraryProvider();
            const header = provider.getHeader('math.h');

            expect(header).not.toBeNull();
            expect(header).toContain('sin');
            expect(header).toContain('cos');
            expect(header).toContain('sqrt');
            expect(header).toContain('M_PI');
        });

        it('should provide assert.h header', () => {
            const provider = new CStandardLibraryProvider();
            const header = provider.getHeader('assert.h');

            expect(header).not.toBeNull();
            expect(header).toContain('assert');
        });

        it('should return null for non-existent headers', () => {
            const provider = new CStandardLibraryProvider();
            const header = provider.getHeader('nonexistent.h');

            expect(header).toBeNull();
        });

        it('should check if header exists', () => {
            const provider = new CStandardLibraryProvider();

            expect(provider.hasHeader('stdio.h')).toBe(true);
            expect(provider.hasHeader('stdlib.h')).toBe(true);
            expect(provider.hasHeader('nonexistent.h')).toBe(false);
        });

        it('should list all available headers', () => {
            const provider = new CStandardLibraryProvider();
            const headers = provider.listHeaders();

            expect(headers).toContain('stdio.h');
            expect(headers).toContain('stdlib.h');
            expect(headers).toContain('string.h');
            expect(headers).toContain('math.h');
            expect(headers).toContain('assert.h');
            expect(headers.length).toBeGreaterThan(0);
        });
    });

    describe('CppStandardLibraryProvider', () => {
        it('should map iostream to stdio.h', () => {
            const provider = new CppStandardLibraryProvider();
            const header = provider.getHeader('iostream');

            expect(header).not.toBeNull();
            expect(header).toContain('printf');
            expect(header).toContain('FILE');
        });

        it('should map cstdio to stdio.h', () => {
            const provider = new CppStandardLibraryProvider();
            const header = provider.getHeader('cstdio');

            expect(header).not.toBeNull();
            expect(header).toContain('printf');
        });

        it('should map cstdlib to stdlib.h', () => {
            const provider = new CppStandardLibraryProvider();
            const header = provider.getHeader('cstdlib');

            expect(header).not.toBeNull();
            expect(header).toContain('malloc');
        });

        it('should map cstring to string.h', () => {
            const provider = new CppStandardLibraryProvider();
            const header = provider.getHeader('cstring');

            expect(header).not.toBeNull();
            expect(header).toContain('strcpy');
        });

        it('should map cmath to math.h', () => {
            const provider = new CppStandardLibraryProvider();
            const header = provider.getHeader('cmath');

            expect(header).not.toBeNull();
            expect(header).toContain('sin');
            expect(header).toContain('sqrt');
        });

        it('should return null for unsupported C++ headers', () => {
            const provider = new CppStandardLibraryProvider();

            expect(provider.getHeader('vector')).toBeNull();
            expect(provider.getHeader('map')).toBeNull();
            expect(provider.getHeader('string')).toBeNull();
        });

        it('should check if C++ header is supported', () => {
            const provider = new CppStandardLibraryProvider();

            expect(provider.hasHeader('iostream')).toBe(true);
            expect(provider.hasHeader('cstdio')).toBe(true);
            expect(provider.hasHeader('vector')).toBe(false);
            expect(provider.hasHeader('map')).toBe(false);
        });

        it('should list all supported headers', () => {
            const provider = new CppStandardLibraryProvider();
            const headers = provider.listHeaders();

            expect(headers).toContain('iostream');
            expect(headers).toContain('cstdio');
            expect(headers).toContain('stdio.h');
            expect(headers.length).toBeGreaterThan(0);
        });

        it('should provide C headers directly', () => {
            const provider = new CppStandardLibraryProvider();
            const header = provider.getHeader('stdio.h');

            expect(header).not.toBeNull();
            expect(header).toContain('printf');
        });

        it('should get mapped header name', () => {
            const provider = new CppStandardLibraryProvider();

            expect(provider.getMappedHeaderName('iostream')).toBe('stdio.h');
            expect(provider.getMappedHeaderName('cstdio')).toBe('stdio.h');
            expect(provider.getMappedHeaderName('vector')).toBeNull();
        });

        it('should list unsupported headers', () => {
            const provider = new CppStandardLibraryProvider();
            const unsupported = provider.listUnsupportedHeaders();

            expect(unsupported).toContain('vector');
            expect(unsupported).toContain('map');
            expect(unsupported).toContain('string');
            expect(unsupported.length).toBeGreaterThan(0);
        });
    });

    describe('Custom Header Provider', () => {
        it('should support custom header provider implementation', () => {
            const customProvider: HeaderProvider = {
                getHeader(name: string) {
                    if (name === 'myheader.h') {
                        return 'struct Point { int x; int y; };';
                    }
                    return null;
                },
                hasHeader(name: string) {
                    return name === 'myheader.h';
                },
                listHeaders() {
                    return ['myheader.h'];
                }
            };

            expect(customProvider.getHeader('myheader.h')).toContain('struct Point');
            expect(customProvider.hasHeader('myheader.h')).toBe(true);
            expect(customProvider.hasHeader('other.h')).toBe(false);
            expect(customProvider.listHeaders()).toEqual(['myheader.h']);
        });

        it('should detect missing custom headers', () => {
            const customProvider: HeaderProvider = {
                getHeader(name: string) {
                    if (name === 'exists.h') {
                        return '// exists';
                    }
                    return null;
                },
                hasHeader(name: string) {
                    return name === 'exists.h';
                },
                listHeaders() {
                    return ['exists.h'];
                }
            };

            expect(customProvider.getHeader('missing.h')).toBeNull();
            expect(customProvider.hasHeader('missing.h')).toBe(false);
        });
    });

    describe('Multi-Header Scenarios', () => {
        it('should handle multiple C standard library headers', () => {
            const provider = new CStandardLibraryProvider();

            const stdio = provider.getHeader('stdio.h');
            const stdlib = provider.getHeader('stdlib.h');
            const string = provider.getHeader('string.h');

            expect(stdio).not.toBeNull();
            expect(stdlib).not.toBeNull();
            expect(string).not.toBeNull();

            expect(stdio).toContain('printf');
            expect(stdlib).toContain('malloc');
            expect(string).toContain('strcpy');
        });

        it('should handle multiple C++ to C mappings', () => {
            const provider = new CppStandardLibraryProvider();

            const iostream = provider.getHeader('iostream');
            const cstdlib = provider.getHeader('cstdlib');
            const cstring = provider.getHeader('cstring');

            expect(iostream).not.toBeNull();
            expect(cstdlib).not.toBeNull();
            expect(cstring).not.toBeNull();

            expect(iostream).toContain('printf');
            expect(cstdlib).toContain('malloc');
            expect(cstring).toContain('strcpy');
        });
    });

    describe('Missing Header Detection', () => {
        it('should detect missing C headers', () => {
            const provider = new CStandardLibraryProvider();

            expect(provider.getHeader('custom/missing.h')).toBeNull();
            expect(provider.hasHeader('custom/missing.h')).toBe(false);
        });

        it('should detect missing C++ headers', () => {
            const provider = new CppStandardLibraryProvider();

            expect(provider.getHeader('custom/missing.hpp')).toBeNull();
            expect(provider.hasHeader('custom/missing.hpp')).toBe(false);
        });

        it('should distinguish between supported and unsupported headers', () => {
            const provider = new CppStandardLibraryProvider();

            // Supported (has C equivalent)
            expect(provider.hasHeader('iostream')).toBe(true);

            // Unsupported (no C equivalent)
            expect(provider.hasHeader('vector')).toBe(false);

            // Missing (not in mapping at all)
            expect(provider.hasHeader('nonexistent.h')).toBe(false);
        });
    });

    describe('Header Provider Interface Compliance', () => {
        it('CStandardLibraryProvider should implement HeaderProvider', () => {
            const provider: HeaderProvider = new CStandardLibraryProvider();

            expect(typeof provider.getHeader).toBe('function');
            expect(typeof provider.hasHeader).toBe('function');
            expect(typeof provider.listHeaders).toBe('function');
        });

        it('CppStandardLibraryProvider should implement HeaderProvider', () => {
            const provider: HeaderProvider = new CppStandardLibraryProvider();

            expect(typeof provider.getHeader).toBe('function');
            expect(typeof provider.hasHeader).toBe('function');
            expect(typeof provider.listHeaders).toBe('function');
        });
    });
});
