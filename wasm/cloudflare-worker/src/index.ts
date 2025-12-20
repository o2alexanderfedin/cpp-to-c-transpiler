/**
 * Cloudflare Worker for C++ to C transpilation
 * Uses minimal WASM build for size optimization
 *
 * NOTE: This worker can only be deployed if the minimal WASM build
 * is < 3MB Brotli compressed (Cloudflare Workers paid tier limit).
 * Run ../scripts/size-check.sh to verify.
 */

interface Env {
    MAX_SOURCE_SIZE: string;
    CACHE_TTL: string;
    CACHE?: KVNamespace;
}

interface TranspileRequest {
    code: string;
    options?: {
        acsl?: {
            statements?: boolean;
            typeInvariants?: boolean;
            axiomatics?: boolean;
            ghostCode?: boolean;
            behaviors?: boolean;
        };
        target?: 'c89' | 'c99' | 'c11' | 'c17';
        optimize?: boolean;
    };
}

interface TranspileResponse {
    success: boolean;
    c?: string;
    acsl?: string;
    diagnostics?: Array<{
        line: number;
        column: number;
        message: string;
        severity: string;
    }>;
    error?: string;
}

/**
 * Simple hash function for cache keys
 */
function hashCode(str: string): string {
    let hash = 0;
    for (let i = 0; i < str.length; i++) {
        hash = ((hash << 5) - hash) + str.charCodeAt(i);
        hash |= 0; // Convert to 32bit integer
    }
    return hash.toString(36);
}

export default {
    async fetch(request: Request, env: Env): Promise<Response> {
        // CORS preflight
        if (request.method === 'OPTIONS') {
            return new Response(null, {
                headers: {
                    'Access-Control-Allow-Origin': '*',
                    'Access-Control-Allow-Methods': 'POST, OPTIONS',
                    'Access-Control-Allow-Headers': 'Content-Type',
                }
            });
        }

        if (request.method !== 'POST') {
            return new Response(JSON.stringify({
                error: 'Method not allowed. Use POST to transpile code.'
            }), {
                status: 405,
                headers: {
                    'Content-Type': 'application/json',
                    'Access-Control-Allow-Origin': '*'
                }
            });
        }

        try {
            const body = await request.json() as TranspileRequest;
            const { code, options } = body;

            if (!code) {
                return Response.json({
                    error: 'Missing required field: code'
                }, {
                    status: 400,
                    headers: { 'Access-Control-Allow-Origin': '*' }
                });
            }

            // Size limit check
            const maxSize = parseInt(env.MAX_SOURCE_SIZE || '100000');
            if (code.length > maxSize) {
                return Response.json({
                    error: `Source code too large (max ${maxSize} bytes)`
                }, {
                    status: 413,
                    headers: { 'Access-Control-Allow-Origin': '*' }
                });
            }

            // Check cache (optional)
            const cacheKey = `transpile:${hashCode(code)}:${JSON.stringify(options || {})}`;
            if (env.CACHE) {
                const cached = await env.CACHE.get(cacheKey);
                if (cached) {
                    return new Response(cached, {
                        headers: {
                            'Content-Type': 'application/json',
                            'X-Cache': 'HIT',
                            'Access-Control-Allow-Origin': '*'
                        }
                    });
                }
            }

            // TODO: Initialize WASM module
            // This requires importing the minimal WASM module
            // For now, return a placeholder response
            const result: TranspileResponse = {
                success: false,
                error: 'WASM module not yet integrated. Please deploy after building WASM.'
            };

            /*
            // Example WASM integration (once module is built):
            import createCppToC from '../wasm/minimal/cpptoc.js';
            import wasmModule from '../wasm/minimal/cpptoc.wasm';

            const module = await createCppToC({ wasmBinary: wasmModule });
            const transpiler = new module.Transpiler();
            const result = transpiler.transpile(code, options || {});
            transpiler.delete();
            */

            const responseBody = JSON.stringify(result);

            // Cache result (optional)
            if (env.CACHE && result.success) {
                const cacheTTL = parseInt(env.CACHE_TTL || '3600');
                await env.CACHE.put(cacheKey, responseBody, {
                    expirationTtl: cacheTTL
                });
            }

            return new Response(responseBody, {
                headers: {
                    'Content-Type': 'application/json',
                    'Access-Control-Allow-Origin': '*',
                    'Cache-Control': `public, max-age=${env.CACHE_TTL || '3600'}`
                }
            });

        } catch (error: unknown) {
            const errorMessage = error instanceof Error ? error.message : 'Unknown error';
            return Response.json({
                success: false,
                error: errorMessage,
                diagnostics: [{
                    line: 0,
                    column: 0,
                    message: errorMessage,
                    severity: 'error'
                }]
            }, {
                status: 500,
                headers: { 'Access-Control-Allow-Origin': '*' }
            });
        }
    }
};
