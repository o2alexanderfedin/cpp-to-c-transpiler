# cpptoc API Server

REST API server for C++ to C transpilation using the cpptoc transpiler.

## Overview

This Node.js/Express API server provides HTTP endpoints for transpiling C++ code to C using the real cpptoc CLI tool (built from TranspilerAPI.cpp with Clang LibTooling).

## Features

- RESTful API with JSON request/response
- Full TypeScript type safety
- Input validation with express-validator
- CORS support for local development
- Security headers with Helmet
- Request logging with Morgan
- Comprehensive error handling
- Health check endpoint

## Architecture

The API follows SOLID principles:

- **Single Responsibility**: Each module has one clear purpose
  - `server.ts`: HTTP routing and middleware
  - `transpiler.ts`: CLI wrapper and process management
  - `types.ts`: Type definitions and interfaces

- **Open/Closed**: Easy to extend with new endpoints or options
- **Dependency Inversion**: Depends on abstractions (TypeScript types)
- **Interface Segregation**: Clean separation of concerns

## Prerequisites

- Node.js >= 18.0.0
- cpptoc CLI built at `../build_working/cpptoc`

## Installation

```bash
cd api
npm install
```

## Build

```bash
npm run build
```

This compiles TypeScript to JavaScript in the `dist/` directory.

## Usage

### Development Mode

```bash
npm run dev
```

Runs the server with ts-node for hot reloading.

### Production Mode

```bash
npm run build
npm start
```

Runs the compiled JavaScript from `dist/`.

### Testing

```bash
npm test
```

Runs the test script to verify API functionality.

## API Endpoints

### Health Check

**GET** `/health`

Check if the API server and cpptoc CLI are available.

**Response:**
```json
{
  "status": "ok",
  "version": "1.0.0",
  "cli": {
    "available": true,
    "version": "cpptoc version 1.0.0"
  },
  "timestamp": "2025-12-22T12:00:00.000Z"
}
```

### API Info

**GET** `/`

Get API information and available endpoints.

**Response:**
```json
{
  "name": "cpptoc API",
  "version": "1.0.0",
  "description": "REST API for C++ to C transpilation",
  "endpoints": {
    "health": "GET /health",
    "transpile": "POST /transpile"
  }
}
```

### Transpile C++ to C

**POST** `/transpile`

Transpile C++ source code to C.

**Request Body:**
```json
{
  "cpp": "int main() { return 0; }",
  "filename": "main.cpp",
  "options": {
    "cppStandard": 17,
    "target": "c99",
    "acsl": {
      "statements": true,
      "typeInvariants": true
    },
    "acslLevel": "basic",
    "acslOutputMode": "inline",
    "enableExceptions": true,
    "enableRTTI": true,
    "monomorphizeTemplates": true,
    "templateInstantiationLimit": 1000,
    "exceptionModel": "sjlj",
    "usePragmaOnce": false,
    "generateDependencyGraph": false
  }
}
```

**Request Fields:**

- `cpp` (required): C++ source code as string
- `filename` (optional): Source filename (default: "input.cpp")
- `options` (optional): Transpilation options (see Options section)

**Response (Success):**
```json
{
  "success": true,
  "c": "/* Generated C code */\nint main(void) { return 0; }",
  "h": "/* Generated header */\n#ifndef MAIN_H\n#define MAIN_H\n...",
  "acsl": "/* ACSL annotations (if separate mode) */",
  "dependencyGraph": "/* DOT graph (if requested) */",
  "diagnostics": [],
  "processingTime": 123,
  "version": "1.0.0"
}
```

**Response (Error):**
```json
{
  "success": false,
  "c": "",
  "h": "",
  "acsl": "",
  "diagnostics": [
    {
      "line": 5,
      "column": 10,
      "severity": "error",
      "message": "expected ';' after expression"
    }
  ],
  "processingTime": 45,
  "version": "1.0.0"
}
```

**Validation Errors:**
```json
{
  "success": false,
  "error": "Validation failed",
  "statusCode": 400,
  "validationErrors": [
    {
      "field": "cpp",
      "message": "cpp field is required and must be a non-empty string"
    }
  ]
}
```

## Transpilation Options

### ACSL Options

Control ACSL (ANSI/ISO C Specification Language) annotation generation:

```typescript
{
  "acsl": {
    "statements": boolean,        // Statement-level annotations
    "typeInvariants": boolean,    // Type invariant annotations
    "axiomatics": boolean,        // Axiomatic definitions
    "ghostCode": boolean,         // Ghost code for verification
    "behaviors": boolean,         // Behavior specifications
    "memoryPredicates": boolean   // Memory predicates (allocable, freeable, etc.)
  },
  "acslLevel": "basic" | "full",  // Coverage level
  "acslOutputMode": "inline" | "separate"  // Output mode
}
```

### C++ Standard

Specify the C++ standard version to parse:

```typescript
{
  "cppStandard": 11 | 14 | 17 | 20 | 23  // Default: 17
}
```

### Target C Standard

Specify the target C standard (currently informational):

```typescript
{
  "target": "c89" | "c99" | "c11" | "c17"  // Default: "c99"
}
```

### Template Options (Phase 11)

Control template monomorphization:

```typescript
{
  "monomorphizeTemplates": boolean,      // Enable/disable (default: true)
  "templateInstantiationLimit": number   // Max instantiations (default: 1000)
}
```

### Exception Handling (Phase 12)

Control exception translation:

```typescript
{
  "enableExceptions": boolean,           // Enable/disable (default: true)
  "exceptionModel": "sjlj" | "tables"    // Model (default: "sjlj")
}
```

### RTTI (Phase 13)

Control RTTI translation:

```typescript
{
  "enableRTTI": boolean  // Enable/disable (default: true)
}
```

### Output Options

Control output format:

```typescript
{
  "usePragmaOnce": boolean,           // Use #pragma once (default: false)
  "generateDependencyGraph": boolean  // Generate DOT graph (default: false)
}
```

## Examples

### Basic Transpilation

```bash
curl -X POST http://localhost:3001/transpile \
  -H "Content-Type: application/json" \
  -d '{
    "cpp": "int add(int a, int b) { return a + b; }"
  }'
```

### With ACSL Annotations

```bash
curl -X POST http://localhost:3001/transpile \
  -H "Content-Type: application/json" \
  -d '{
    "cpp": "int factorial(int n) { if (n <= 1) return 1; return n * factorial(n-1); }",
    "options": {
      "acsl": {
        "statements": true
      },
      "acslLevel": "full"
    }
  }'
```

### With Custom C++ Standard

```bash
curl -X POST http://localhost:3001/transpile \
  -H "Content-Type: application/json" \
  -d '{
    "cpp": "auto x = 42;",
    "options": {
      "cppStandard": 20
    }
  }'
```

## Error Handling

The API returns appropriate HTTP status codes:

- `200 OK`: Successful transpilation
- `400 Bad Request`: Invalid input or transpilation errors
- `404 Not Found`: Endpoint not found
- `500 Internal Server Error`: Unexpected server error
- `503 Service Unavailable`: cpptoc CLI not available

All error responses include a JSON body with:
- `success: false`
- `error`: Error message
- `statusCode`: HTTP status code
- `validationErrors` (optional): Field-level validation errors

## Configuration

Environment variables:

- `PORT`: Server port (default: 3001)

## Development

### Linting

```bash
npm run lint        # Check for issues
npm run lint:fix    # Auto-fix issues
```

### File Structure

```
api/
├── src/
│   ├── server.ts      # Express server and routes
│   ├── transpiler.ts  # CLI wrapper
│   └── types.ts       # TypeScript types
├── test/
│   └── test-api.ts    # Test script
├── package.json
├── tsconfig.json
├── .eslintrc.json
├── .gitignore
└── README.md
```

## How It Works

### CLI Wrapper

The `transpiler.ts` module wraps the cpptoc CLI tool:

1. Creates a temporary directory for the transpilation
2. Writes C++ source to a temp file
3. Builds CLI arguments from options
4. Spawns the cpptoc process
5. Captures stdout/stderr
6. Reads generated .c/.h files
7. Parses diagnostics from stderr
8. Cleans up temp files
9. Returns TranspileResult

### Real Transpilation

This API uses the **REAL** cpptoc transpiler built from TranspilerAPI.cpp:

- Real Clang LibTooling implementation
- Real C++ AST parsing and analysis
- Real C code generation
- NO placeholders or mock code

The transpiler calls `cpptoc::transpile()` which:
1. Parses C++ with Clang
2. Traverses AST with CppToCVisitor
3. Builds C nodes with CNodeBuilder
4. Generates C code with CodeGenerator
5. Optionally generates ACSL with ACSLGenerator

## License

MIT
