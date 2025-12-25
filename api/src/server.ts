/**
 * Express API server for C++ to C transpilation
 *
 * This server provides a REST API endpoint for transpiling C++ code to C
 * using the cpptoc CLI tool.
 *
 * SOLID Principles:
 * - Single Responsibility: Server only handles HTTP routing
 * - Dependency Inversion: Depends on transpiler abstraction
 * - Open/Closed: Easy to add new endpoints without modifying existing code
 */

import express, { Request, Response, NextFunction } from 'express';
import cors from 'cors';
import helmet from 'helmet';
import morgan from 'morgan';
import { body, validationResult } from 'express-validator';
import { transpile, checkCLI, getCLIVersion } from './transpiler';
import type {
  TranspileRequest,
  TranspileResponse,
  ErrorResponse,
} from './types';

// API configuration
const PORT = process.env.PORT || 3001;
const API_VERSION = '1.0.0';

// Create Express app
const app = express();

// Middleware
app.use(helmet()); // Security headers
app.use(cors()); // Enable CORS for local development
app.use(express.json({ limit: '10mb' })); // Parse JSON bodies (10MB limit for large C++ files)
app.use(morgan('combined')); // HTTP request logging

/**
 * Health check endpoint
 * GET /health
 */
app.get('/health', async (_req: Request, res: Response) => {
  const cliAvailable = await checkCLI();
  const cliVersion = await getCLIVersion();

  res.json({
    status: 'ok',
    version: API_VERSION,
    cli: {
      available: cliAvailable,
      version: cliVersion,
    },
    timestamp: new Date().toISOString(),
  });
});

/**
 * API info endpoint
 * GET /
 */
app.get('/', (_req: Request, res: Response) => {
  res.json({
    name: 'cpptoc API',
    version: API_VERSION,
    description: 'REST API for C++ to C transpilation',
    endpoints: {
      health: 'GET /health',
      transpile: 'POST /transpile',
    },
    documentation: 'https://github.com/your-repo/hupyy-cpp-to-c',
  });
});

/**
 * Transpile endpoint
 * POST /transpile
 *
 * Request body:
 * {
 *   "cpp": "int main() { return 0; }",
 *   "filename": "main.cpp",
 *   "options": { ... }
 * }
 *
 * Response:
 * {
 *   "success": true,
 *   "c": "...",
 *   "h": "...",
 *   "acsl": "...",
 *   "diagnostics": [...],
 *   "processingTime": 123,
 *   "version": "1.0.0"
 * }
 */
app.post(
  '/transpile',
  // Validation middleware
  [
    body('cpp')
      .isString()
      .notEmpty()
      .withMessage('cpp field is required and must be a non-empty string'),
    body('filename')
      .optional()
      .isString()
      .matches(/^[\w\-. ]+\.(cpp|cc|cxx)$/)
      .withMessage('filename must be a valid C++ filename'),
    body('options')
      .optional()
      .isObject()
      .withMessage('options must be an object'),
    body('options.cppStandard')
      .optional()
      .isInt({ min: 11, max: 23 })
      .withMessage('cppStandard must be 11, 14, 17, 20, or 23'),
    body('options.acslLevel')
      .optional()
      .isIn(['basic', 'full'])
      .withMessage('acslLevel must be "basic" or "full"'),
    body('options.acslOutputMode')
      .optional()
      .isIn(['inline', 'separate'])
      .withMessage('acslOutputMode must be "inline" or "separate"'),
    body('options.target')
      .optional()
      .isIn(['c89', 'c99', 'c11', 'c17'])
      .withMessage('target must be c89, c99, c11, or c17'),
    body('options.exceptionModel')
      .optional()
      .isIn(['sjlj', 'tables'])
      .withMessage('exceptionModel must be "sjlj" or "tables"'),
  ],
  async (req: Request, res: Response) => {
    // Check validation errors
    const errors = validationResult(req);
    if (!errors.isEmpty()) {
      const errorResponse: ErrorResponse = {
        success: false,
        error: 'Validation failed',
        statusCode: 400,
        validationErrors: errors.array().map((err) => ({
          field: ('param' in err ? err.param : 'unknown') as string,
          message: String(err.msg),
        })),
      };
      res.status(400).json(errorResponse);
      return;
    }

    // Extract request data
    const requestData: TranspileRequest = req.body;
    const { cpp, filename = 'input.cpp', options = {} } = requestData;

    // Check if CLI is available
    const cliAvailable = await checkCLI();
    if (!cliAvailable) {
      const errorResponse: ErrorResponse = {
        success: false,
        error: 'cpptoc CLI is not available or not executable',
        statusCode: 503,
      };
      return res.status(503).json(errorResponse);
    }

    try {
      // Start timing
      const startTime = Date.now();

      // Transpile C++ to C
      const result = await transpile(cpp, filename, options);

      // Calculate processing time
      const processingTime = Date.now() - startTime;

      // Build response
      const response: TranspileResponse = {
        ...result,
        processingTime,
        version: API_VERSION,
      };

      // Return appropriate status code based on success
      const statusCode = result.success ? 200 : 400;
      res.status(statusCode).json(response);
      return;
    } catch (error) {
      // Handle unexpected errors
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';

      const errorResponse: ErrorResponse = {
        success: false,
        error: `Transpilation failed: ${errorMessage}`,
        statusCode: 500,
      };

      res.status(500).json(errorResponse);
      return;
    }
  }
);

/**
 * 404 handler
 */
app.use((_req: Request, res: Response) => {
  const errorResponse: ErrorResponse = {
    success: false,
    error: 'Endpoint not found',
    statusCode: 404,
  };
  res.status(404).json(errorResponse);
});

/**
 * Error handler middleware
 */
app.use((err: Error, _req: Request, res: Response, _next: NextFunction) => {
  console.error('Unhandled error:', err);

  const errorResponse: ErrorResponse = {
    success: false,
    error: err.message || 'Internal server error',
    statusCode: 500,
  };

  res.status(500).json(errorResponse);
});

/**
 * Start server
 */
async function startServer() {
  // Check if CLI is available on startup
  const cliAvailable = await checkCLI();
  if (!cliAvailable) {
    console.error('WARNING: cpptoc CLI is not available or not executable');
    console.error('Make sure to build the project first: cd .. && ./build.sh');
  } else {
    const cliVersion = await getCLIVersion();
    console.log(`cpptoc CLI available: ${cliVersion}`);
  }

  // Start listening
  app.listen(PORT, () => {
    console.log(`cpptoc API server running on http://localhost:${PORT}`);
    console.log(`API version: ${API_VERSION}`);
    console.log(`Health check: http://localhost:${PORT}/health`);
    console.log(`Transpile endpoint: POST http://localhost:${PORT}/transpile`);
  });
}

// Start server if this file is run directly
if (require.main === module) {
  startServer().catch((err) => {
    console.error('Failed to start server:', err);
    process.exit(1);
  });
}

// Export app for testing
export default app;
