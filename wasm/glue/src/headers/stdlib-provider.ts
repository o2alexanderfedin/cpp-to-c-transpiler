/**
 * C Standard Library Header Provider
 * Provides common C standard library headers for WebAssembly transpilation
 */

import { HeaderProvider } from '../types.js';

/**
 * Minimal stdio.h declarations for transpilation
 */
const STDIO_H = `
#ifndef _STDIO_H
#define _STDIO_H

#include <stddef.h>
#include <stdarg.h>

typedef struct _FILE FILE;

extern FILE *stdin;
extern FILE *stdout;
extern FILE *stderr;

int printf(const char *format, ...);
int fprintf(FILE *stream, const char *format, ...);
int sprintf(char *str, const char *format, ...);
int snprintf(char *str, size_t size, const char *format, ...);

int scanf(const char *format, ...);
int fscanf(FILE *stream, const char *format, ...);
int sscanf(const char *str, const char *format, ...);

FILE *fopen(const char *filename, const char *mode);
int fclose(FILE *stream);
int fflush(FILE *stream);

size_t fread(void *ptr, size_t size, size_t nmemb, FILE *stream);
size_t fwrite(const void *ptr, size_t size, size_t nmemb, FILE *stream);

int fgetc(FILE *stream);
int fputc(int c, FILE *stream);
char *fgets(char *s, int size, FILE *stream);
int fputs(const char *s, FILE *stream);

int getchar(void);
int putchar(int c);
char *gets(char *s);
int puts(const char *s);

int fseek(FILE *stream, long offset, int whence);
long ftell(FILE *stream);
void rewind(FILE *stream);

void perror(const char *s);

#define EOF (-1)
#define SEEK_SET 0
#define SEEK_CUR 1
#define SEEK_END 2

#endif
`;

/**
 * Minimal stdlib.h declarations for transpilation
 */
const STDLIB_H = `
#ifndef _STDLIB_H
#define _STDLIB_H

#include <stddef.h>

void *malloc(size_t size);
void *calloc(size_t nmemb, size_t size);
void *realloc(void *ptr, size_t size);
void free(void *ptr);

int atoi(const char *nptr);
long atol(const char *nptr);
long long atoll(const char *nptr);
double atof(const char *nptr);

long strtol(const char *nptr, char **endptr, int base);
unsigned long strtoul(const char *nptr, char **endptr, int base);
double strtod(const char *nptr, char **endptr);

void abort(void);
void exit(int status);
int atexit(void (*function)(void));

char *getenv(const char *name);
int system(const char *command);

void qsort(void *base, size_t nmemb, size_t size,
           int (*compar)(const void *, const void *));
void *bsearch(const void *key, const void *base, size_t nmemb, size_t size,
              int (*compar)(const void *, const void *));

int abs(int j);
long labs(long j);

int rand(void);
void srand(unsigned int seed);

#define EXIT_SUCCESS 0
#define EXIT_FAILURE 1
#define RAND_MAX 2147483647

#endif
`;

/**
 * Minimal string.h declarations for transpilation
 */
const STRING_H = `
#ifndef _STRING_H
#define _STRING_H

#include <stddef.h>

void *memcpy(void *dest, const void *src, size_t n);
void *memmove(void *dest, const void *src, size_t n);
void *memset(void *s, int c, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);
void *memchr(const void *s, int c, size_t n);

char *strcpy(char *dest, const char *src);
char *strncpy(char *dest, const char *src, size_t n);
char *strcat(char *dest, const char *src);
char *strncat(char *dest, const char *src, size_t n);

int strcmp(const char *s1, const char *s2);
int strncmp(const char *s1, const char *s2, size_t n);

char *strchr(const char *s, int c);
char *strrchr(const char *s, int c);
char *strstr(const char *haystack, const char *needle);

size_t strlen(const char *s);
size_t strnlen(const char *s, size_t maxlen);

char *strdup(const char *s);
char *strndup(const char *s, size_t n);

char *strtok(char *str, const char *delim);

char *strerror(int errnum);

#endif
`;

/**
 * Minimal math.h declarations for transpilation
 */
const MATH_H = `
#ifndef _MATH_H
#define _MATH_H

double sin(double x);
double cos(double x);
double tan(double x);
double asin(double x);
double acos(double x);
double atan(double x);
double atan2(double y, double x);

double sinh(double x);
double cosh(double x);
double tanh(double x);

double exp(double x);
double log(double x);
double log10(double x);
double log2(double x);

double pow(double x, double y);
double sqrt(double x);
double cbrt(double x);

double fabs(double x);
double ceil(double x);
double floor(double x);
double trunc(double x);
double round(double x);

double fmod(double x, double y);
double remainder(double x, double y);

double fmin(double x, double y);
double fmax(double x, double y);

#define M_E        2.71828182845904523536
#define M_LOG2E    1.44269504088896340736
#define M_LOG10E   0.43429448190325182765
#define M_LN2      0.69314718055994530942
#define M_LN10     2.30258509299404568402
#define M_PI       3.14159265358979323846
#define M_PI_2     1.57079632679489661923
#define M_PI_4     0.78539816339744830962
#define M_1_PI     0.31830988618379067154
#define M_2_PI     0.63661977236758134308

#endif
`;

/**
 * Minimal assert.h declarations for transpilation
 */
const ASSERT_H = `
#ifndef _ASSERT_H
#define _ASSERT_H

#ifdef NDEBUG
#define assert(expression) ((void)0)
#else
extern void __assert_fail(const char *assertion, const char *file,
                          unsigned int line, const char *function);
#define assert(expression) \\
    ((expression) ? (void)0 : __assert_fail(#expression, __FILE__, __LINE__, __func__))
#endif

#endif
`;

/**
 * Minimal stddef.h declarations for transpilation
 */
const STDDEF_H = `
#ifndef _STDDEF_H
#define _STDDEF_H

typedef unsigned long size_t;
typedef long ptrdiff_t;

#ifndef NULL
#define NULL ((void *)0)
#endif

#define offsetof(type, member) ((size_t)&((type *)0)->member)

#endif
`;

/**
 * Minimal stdarg.h declarations for transpilation
 */
const STDARG_H = `
#ifndef _STDARG_H
#define _STDARG_H

typedef __builtin_va_list va_list;

#define va_start(ap, last) __builtin_va_start(ap, last)
#define va_arg(ap, type) __builtin_va_arg(ap, type)
#define va_end(ap) __builtin_va_end(ap)
#define va_copy(dest, src) __builtin_va_copy(dest, src)

#endif
`;

/**
 * C Standard Library Header Provider
 * Provides common C standard library headers for WebAssembly transpilation
 */
export class CStandardLibraryProvider implements HeaderProvider {
    private headers = new Map<string, string>([
        ['stdio.h', STDIO_H],
        ['stdlib.h', STDLIB_H],
        ['string.h', STRING_H],
        ['math.h', MATH_H],
        ['assert.h', ASSERT_H],
        ['stddef.h', STDDEF_H],
        ['stdarg.h', STDARG_H],
    ]);

    getHeader(name: string): string | null {
        return this.headers.get(name) || null;
    }

    hasHeader(name: string): boolean {
        return this.headers.has(name);
    }

    listHeaders(): string[] {
        return Array.from(this.headers.keys());
    }
}
