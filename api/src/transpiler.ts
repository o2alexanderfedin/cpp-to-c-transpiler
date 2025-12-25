/**
 * CLI wrapper module for cpptoc transpiler
 *
 * This module wraps the cpptoc CLI executable and provides a clean Node.js API.
 * SOLID Principles:
 * - Single Responsibility: Only responsible for calling CLI and parsing output
 * - Dependency Inversion: Depends on TranspileOptions abstraction
 * - Open/Closed: Options can be extended without modifying this code
 */

import { spawn } from 'child_process';
import { writeFile, unlink, mkdir } from 'fs/promises';
import { join } from 'path';
import { tmpdir } from 'os';
import { randomBytes } from 'crypto';
import type {
  TranspileOptions,
  TranspileResult,
  Diagnostic,
} from './types';

/**
 * Path to transpiler-api-cli executable
 * This is a JSON-outputting wrapper around TranspilerAPI.cpp
 * When running with ts-node: __dirname = /Users/.../api/src
 * When running compiled: __dirname = /Users/.../api/dist
 * We need to go up to the project root: api -> hupyy-cpp-to-c
 */
const TRANSPILER_CLI_PATH = join(__dirname, '../..', 'build_working', 'transpiler-api-cli');

/**
 * Parse CLI arguments from TranspileOptions
 * Maps API options to CLI flags
 * NOTE: Currently unused as transpiler-api-cli doesn't support options yet
 * Kept for future enhancement when we add option support to the wrapper
 */
/* Commented out until transpiler-api-cli supports options
function buildCLIArgs(options: TranspileOptions = {}): string[] {
  const args: string[] = [];

  // ACSL options
  if (options.acsl) {
    const acsl = options.acsl;
    const hasAnyACSL = Object.values(acsl).some(v => v === true);

    if (hasAnyACSL) {
      args.push('--generate-acsl');

      // ACSL level
      if (options.acslLevel) {
        args.push(`--acsl-level=${options.acslLevel}`);
      }

      // ACSL output mode
      if (options.acslOutputMode) {
        args.push(`--acsl-output=${options.acslOutputMode}`);
      }

      // Memory predicates
      if (acsl.memoryPredicates) {
        args.push('--acsl-memory-predicates');
      }
    }
  }

  // C++ standard
  if (options.cppStandard) {
    args.push(`--extra-arg=-std=c++${options.cppStandard}`);
  }

  // Template monomorphization
  if (options.monomorphizeTemplates === false) {
    // CLI flag enables it by default, so only add if explicitly disabled
    // Note: CLI doesn't have a --no-template-monomorphization flag
    // We'll handle this in future iterations
  }

  // Template instantiation limit
  if (options.templateInstantiationLimit !== undefined) {
    args.push(`--template-instantiation-limit=${options.templateInstantiationLimit}`);
  }

  // Exception handling
  if (options.enableExceptions === false) {
    args.push('--extra-arg=-fno-exceptions');
  }

  if (options.exceptionModel) {
    args.push(`--exception-model=${options.exceptionModel}`);
  }

  // RTTI
  if (options.enableRTTI === false) {
    args.push('--extra-arg=-fno-rtti');
  }

  // Pragma once
  if (options.usePragmaOnce) {
    args.push('--use-pragma-once');
  }

  // Dependency graph
  if (options.generateDependencyGraph) {
    args.push('--visualize-deps');
  }

  return args;
}
*/

/**
 * Parse diagnostic messages from CLI stderr output
 * Extracts error, warning, and note messages
 */
function parseDiagnostics(stderr: string): Diagnostic[] {
  const diagnostics: Diagnostic[] = [];
  const lines = stderr.split('\n');

  for (const line of lines) {
    // Skip empty lines
    if (!line.trim()) continue;

    // Parse Clang-style diagnostics: filename:line:column: severity: message
    const match = line.match(/^(.+?):(\d+):(\d+):\s+(error|warning|note):\s+(.+)$/);
    if (match) {
      const [, , lineStr, colStr, severity, message] = match;
      diagnostics.push({
        line: parseInt(lineStr, 10),
        column: parseInt(colStr, 10),
        severity: severity as 'error' | 'warning' | 'note',
        message: message.trim(),
      });
    } else if (line.includes('error:') || line.includes('warning:') || line.includes('note:')) {
      // Fallback: parse simpler diagnostic format
      const severity = line.includes('error:') ? 'error'
        : line.includes('warning:') ? 'warning'
        : 'note';

      diagnostics.push({
        line: 0,
        column: 0,
        severity,
        message: line.trim(),
      });
    }
  }

  return diagnostics;
}

/**
 * Transpile C++ code to C using cpptoc CLI
 *
 * IMPLEMENTATION APPROACH:
 * 1. Create temporary directory for input/output files
 * 2. Write C++ source to temp file
 * 3. Build CLI arguments from options
 * 4. Execute cpptoc CLI with arguments
 * 5. Read generated .c and .h files
 * 6. Parse diagnostics from stderr
 * 7. Clean up temp files
 * 8. Return TranspileResult
 *
 * @param cppSource C++ source code to transpile
 * @param filename Source filename (for error messages)
 * @param options Transpilation configuration options
 * @returns Promise<TranspileResult> with generated code and diagnostics
 */
export async function transpile(
  cppSource: string,
  filename: string = 'input.cpp',
  _options: TranspileOptions = {}
): Promise<TranspileResult> {
  // Create unique temporary directory for this transpilation
  const tempDir = join(tmpdir(), `cpptoc-${randomBytes(8).toString('hex')}`);
  await mkdir(tempDir, { recursive: true });

  const inputPath = join(tempDir, filename);
  const outputBaseName = filename.replace(/\.(cpp|cc|cxx)$/, '');
  const outputCPath = join(tempDir, `${outputBaseName}.c`);
  const outputHPath = join(tempDir, `${outputBaseName}.h`);
  const outputACSLPath = join(tempDir, `${outputBaseName}.acsl`);
  const depsPath = join(tempDir, 'deps.dot');

  try {
    // Write C++ source to temp file
    await writeFile(inputPath, cppSource, 'utf-8');

    // Build CLI arguments - for transpiler-api-cli, we just pass the file and --json
    // The buildCLIArgs function is for the old cpptoc CLI which doesn't work properly
    // For now, we use default options and just pass the input file
    const args = [inputPath, '--json'];

    // Execute transpiler-api-cli
    const result = await new Promise<{
      stdout: string;
      stderr: string;
      exitCode: number;
    }>((resolve, reject) => {
      const proc = spawn(TRANSPILER_CLI_PATH, args, {
        cwd: tempDir,
        env: process.env,
      });

      let stdout = '';
      let stderr = '';

      proc.stdout.on('data', (data) => {
        stdout += data.toString();
      });

      proc.stderr.on('data', (data) => {
        stderr += data.toString();
      });

      proc.on('error', (err) => {
        reject(new Error(`Failed to execute cpptoc: ${err.message}`));
      });

      proc.on('close', (code) => {
        resolve({
          stdout,
          stderr,
          exitCode: code || 0,
        });
      });
    });

    // Parse JSON output from transpiler-api-cli
    // The CLI outputs JSON to stdout, but also debug messages to stdout
    // We need to extract just the JSON part
    // The JSON starts with a line containing just "{" and ends with a line containing just "}"
    try {
      const lines = result.stdout.split('\n');

      // Find the start of JSON (line with just "{")
      let jsonStart = -1;
      for (let i = lines.length - 1; i >= 0; i--) {
        if (lines[i].trim() === '{') {
          jsonStart = i;
          break;
        }
      }

      if (jsonStart === -1) {
        throw new Error('No JSON output found in transpiler response');
      }

      // Extract JSON lines from start to end
      const jsonLines = lines.slice(jsonStart);
      const jsonStr = jsonLines.join('\n');
      const jsonOutput = JSON.parse(jsonStr);

      return {
        success: jsonOutput.success || false,
        c: jsonOutput.c || '',
        h: jsonOutput.h || '',
        acsl: jsonOutput.acsl || '',
        dependencyGraph: jsonOutput.dependencyGraph || '',
        diagnostics: jsonOutput.diagnostics || [],
      };
    } catch (parseError) {
      // Failed to parse JSON - likely a CLI error
      const diagnostics = parseDiagnostics(result.stderr);

      // If we couldn't parse stderr diagnostics, add a generic error
      if (diagnostics.length === 0) {
        diagnostics.push({
          line: 0,
          column: 0,
          severity: 'error',
          message: `Failed to parse transpiler output: ${parseError instanceof Error ? parseError.message : String(parseError)}`,
        });
      }

      return {
        success: false,
        c: '',
        h: '',
        acsl: '',
        diagnostics,
      };
    }
  } catch (error) {
    // Handle errors
    const errorMessage = error instanceof Error ? error.message : String(error);

    return {
      success: false,
      c: '',
      h: '',
      acsl: '',
      diagnostics: [
        {
          line: 0,
          column: 0,
          severity: 'error',
          message: `Transpilation failed: ${errorMessage}`,
        },
      ],
    };
  } finally {
    // Clean up temp files (best effort)
    try {
      await unlink(inputPath).catch(() => {});
      await unlink(outputCPath).catch(() => {});
      await unlink(outputHPath).catch(() => {});
      await unlink(outputACSLPath).catch(() => {});
      await unlink(depsPath).catch(() => {});
      // Note: Not removing tempDir itself as it may contain other files
    } catch {
      // Ignore cleanup errors
    }
  }
}

/**
 * Safely read a file, returning empty string if it doesn't exist
 * NOTE: Currently unused but kept for fallback scenarios
 */
/* Commented out until needed for fallback
async function readFileSafe(path: string): Promise<string> {
  try {
    const { readFile } = await import('fs/promises');
    return await readFile(path, 'utf-8');
  } catch {
    return '';
  }
}
*/

/**
 * Check if cpptoc CLI executable exists and is accessible
 */
export async function checkCLI(): Promise<boolean> {
  try {
    const { access } = await import('fs/promises');
    const { constants } = await import('fs');
    await access(TRANSPILER_CLI_PATH, constants.X_OK);
    return true;
  } catch {
    return false;
  }
}

/**
 * Get cpptoc CLI version
 */
export async function getCLIVersion(): Promise<string> {
  try {
    const result = await new Promise<string>((resolve, reject) => {
      const proc = spawn(TRANSPILER_CLI_PATH, ['--version']);

      let output = '';

      proc.stdout.on('data', (data) => {
        output += data.toString();
      });

      proc.stderr.on('data', (data) => {
        output += data.toString();
      });

      proc.on('error', (err) => {
        reject(err);
      });

      proc.on('close', () => {
        resolve(output.trim());
      });
    });

    return result || 'unknown';
  } catch {
    return 'unknown';
  }
}
