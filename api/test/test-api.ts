/**
 * Test script for cpptoc API
 *
 * This script tests the API functionality by making HTTP requests
 * to the transpile endpoint and verifying the responses.
 */

import http from 'http';
import type { TranspileRequest, TranspileResponse } from '../src/types';

const API_URL = process.env.API_URL || 'http://localhost:3001';
const GREEN = '\x1b[32m';
const RED = '\x1b[31m';
const YELLOW = '\x1b[33m';
const RESET = '\x1b[0m';

/**
 * Make POST request to API
 */
async function post(endpoint: string, data: unknown): Promise<unknown> {
  return new Promise((resolve, reject) => {
    const url = new URL(endpoint, API_URL);
    const body = JSON.stringify(data);

    const options = {
      hostname: url.hostname,
      port: url.port,
      path: url.pathname,
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Content-Length': Buffer.byteLength(body),
      },
    };

    const req = http.request(options, (res) => {
      let responseBody = '';

      res.on('data', (chunk) => {
        responseBody += chunk;
      });

      res.on('end', () => {
        try {
          const json = JSON.parse(responseBody);
          resolve(json);
        } catch {
          reject(new Error(`Failed to parse JSON: ${responseBody}`));
        }
      });
    });

    req.on('error', reject);
    req.write(body);
    req.end();
  });
}

/**
 * Make GET request to API
 */
async function get(endpoint: string): Promise<unknown> {
  return new Promise((resolve, reject) => {
    const url = new URL(endpoint, API_URL);

    const options = {
      hostname: url.hostname,
      port: url.port,
      path: url.pathname,
      method: 'GET',
    };

    const req = http.request(options, (res) => {
      let responseBody = '';

      res.on('data', (chunk) => {
        responseBody += chunk;
      });

      res.on('end', () => {
        try {
          const json = JSON.parse(responseBody);
          resolve(json);
        } catch {
          reject(new Error(`Failed to parse JSON: ${responseBody}`));
        }
      });
    });

    req.on('error', reject);
    req.end();
  });
}

/**
 * Test case interface
 */
interface TestCase {
  name: string;
  request: TranspileRequest;
  validate: (response: TranspileResponse) => boolean;
  expectSuccess: boolean;
}

/**
 * Test cases
 */
const tests: TestCase[] = [
  {
    name: 'Simple main function',
    request: {
      cpp: 'int main() { return 0; }',
      filename: 'main.cpp',
    },
    validate: (response) => {
      return (
        response.success === true &&
        response.c.length > 0 &&
        response.c.includes('main') &&
        !response.c.includes('PLACEHOLDER')
      );
    },
    expectSuccess: true,
  },
  {
    name: 'Simple function with parameters',
    request: {
      cpp: 'int add(int a, int b) { return a + b; }',
      filename: 'add.cpp',
    },
    validate: (response) => {
      return (
        response.success === true &&
        response.c.length > 0 &&
        response.c.includes('add') &&
        !response.c.includes('PLACEHOLDER')
      );
    },
    expectSuccess: true,
  },
  {
    name: 'Class with methods',
    request: {
      cpp: `
        class Calculator {
        public:
          int add(int a, int b) { return a + b; }
          int subtract(int a, int b) { return a - b; }
        };
      `,
      filename: 'calculator.cpp',
    },
    validate: (response) => {
      return (
        response.success === true &&
        response.c.length > 0 &&
        (response.c.includes('Calculator') || response.c.includes('add')) &&
        !response.c.includes('PLACEHOLDER')
      );
    },
    expectSuccess: true,
  },
  {
    name: 'With ACSL annotations',
    request: {
      cpp: 'int factorial(int n) { if (n <= 1) return 1; return n * factorial(n-1); }',
      filename: 'factorial.cpp',
      options: {
        acsl: {
          statements: true,
        },
        acslLevel: 'basic',
        acslOutputMode: 'inline',
      },
    },
    validate: (response) => {
      return (
        response.success === true &&
        response.c.length > 0 &&
        response.c.includes('factorial') &&
        !response.c.includes('PLACEHOLDER')
      );
    },
    expectSuccess: true,
  },
  {
    name: 'With C++17 features',
    request: {
      cpp: 'auto add(int a, int b) { return a + b; }',
      filename: 'auto.cpp',
      options: {
        cppStandard: 17,
      },
    },
    validate: (response) => {
      return (
        response.success === true &&
        response.c.length > 0 &&
        response.c.includes('add') &&
        !response.c.includes('PLACEHOLDER')
      );
    },
    expectSuccess: true,
  },
  {
    name: 'Invalid C++ code (should fail)',
    request: {
      cpp: 'int main() { invalid syntax here }',
      filename: 'invalid.cpp',
    },
    validate: (response) => {
      return (
        response.success === false &&
        response.diagnostics.length > 0 &&
        response.diagnostics.some(d => d.severity === 'error')
      );
    },
    expectSuccess: false,
  },
];

/**
 * Run all tests
 */
async function runTests() {
  console.log(`${YELLOW}cpptoc API Test Suite${RESET}\n`);
  console.log(`Testing API at: ${API_URL}\n`);

  // Test health endpoint first
  console.log('Testing health endpoint...');
  try {
    const health = await get('/health');
    console.log(`${GREEN}✓${RESET} Health check passed`);
    console.log(`  Response:`, JSON.stringify(health, null, 2));
  } catch (err) {
    console.error(`${RED}✗${RESET} Health check failed:`, err);
    console.error(`${RED}Make sure the API server is running: npm run dev${RESET}`);
    process.exit(1);
  }

  console.log('');

  // Run test cases
  let passed = 0;
  let failed = 0;

  for (const test of tests) {
    console.log(`Testing: ${test.name}`);

    try {
      const response = await post('/transpile', test.request) as TranspileResponse;

      // Validate response
      const valid = test.validate(response);

      if (valid) {
        console.log(`${GREEN}✓${RESET} Test passed`);
        console.log(`  Processing time: ${response.processingTime}ms`);

        if (response.success) {
          console.log(`  C code length: ${response.c.length} bytes`);
          console.log(`  H code length: ${response.h.length} bytes`);

          // Show first few lines of C code to verify it's real
          const cLines = response.c.split('\n').slice(0, 3);
          console.log(`  C code preview:`);
          cLines.forEach(line => console.log(`    ${line}`));
        } else {
          console.log(`  Diagnostics: ${response.diagnostics.length}`);
          if (response.diagnostics.length > 0) {
            console.log(`  First error: ${response.diagnostics[0].message}`);
          }
        }

        passed++;
      } else {
        console.log(`${RED}✗${RESET} Test failed - validation failed`);
        console.log(`  Response:`, JSON.stringify(response, null, 2));
        failed++;
      }
    } catch (err) {
      console.log(`${RED}✗${RESET} Test failed - exception thrown`);
      console.error('  Error:', err);
      failed++;
    }

    console.log('');
  }

  // Summary
  console.log(`${YELLOW}Test Summary${RESET}`);
  console.log(`  Total: ${tests.length}`);
  console.log(`  ${GREEN}Passed: ${passed}${RESET}`);
  console.log(`  ${failed > 0 ? RED : GREEN}Failed: ${failed}${RESET}`);

  if (failed === 0) {
    console.log(`\n${GREEN}All tests passed!${RESET}`);
    process.exit(0);
  } else {
    console.log(`\n${RED}Some tests failed${RESET}`);
    process.exit(1);
  }
}

// Run tests
runTests().catch((err) => {
  console.error(`${RED}Test suite failed:${RESET}`, err);
  process.exit(1);
});
