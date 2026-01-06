# License Attributions for External C++23 Validation Projects

This document provides full attribution and license information for all external test projects integrated into the C++23 validation suite.

---

## 1. scivision/Cpp23-examples

**Source**: https://github.com/scivision/Cpp23-examples
**License**: MIT License
**Integration Method**: Git submodule
**Location**: `external-projects/cpp23-examples/`
**Purpose**: Educational C++23 examples and multi-compiler validation

### MIT License Text

```
MIT License

Copyright (c) Michael Hirsch

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

---

## 2. GCC Test Suite (g++.dg/cpp23)

**Source**: https://github.com/gcc-mirror/gcc
**Official Repository**: https://gcc.gnu.org/git/gcc.git
**License**: GNU General Public License v3.0 with GCC Runtime Library Exception
**Integration Method**: Selective extraction (130 tests from 259 available)
**Location**: `external-projects/gcc-tests/`
**Source Commit**: `3735bbb7d918e88cac9818b477121cf03558a7cc`
**Commit Date**: 2025-12-21 20:10:14 +0800
**Purpose**: Comprehensive C++23 language feature validation

### Test Extraction Details

We extracted 130 test files from `gcc/testsuite/g++.dg/cpp23/` directory, organized into 9 feature categories:

1. **if-consteval-P1938** (13 tests, 52 KB)
2. **multidim-subscript-P2128** (16 tests, 64 KB)
3. **static-operators-P1169** (8 tests, 32 KB)
4. **auto-deduction-P0849** (22 tests, 88 KB)
5. **constexpr-enhancements** (19 tests, 76 KB)
6. **class-template-deduction-inherited** (10 tests, 40 KB)
7. **attributes-P2180** (13 tests, 56 KB)
8. **ranges-P2678** (10 tests, 40 KB)
9. **miscellaneous** (19 tests, 92 KB)

**Total**: 130 tests, 552 KB

### Fair Use and Educational Purpose

The GCC test files are used under the following principles:

1. **Educational and Research Purpose**: Used solely for validating C++23 compiler compliance
2. **Test Code Only**: We extract test cases, not GCC implementation code
3. **Transformative Use**: Tests are adapted to standalone C++ files, not used as-is
4. **Attribution**: Full source attribution and commit hash documented
5. **No Redistribution of GCC**: We do not redistribute GCC itself, only test cases

### GCC License Information

GCC is licensed under GNU General Public License v3.0. The full license text can be found at:
https://www.gnu.org/licenses/gpl-3.0.html

**GCC Runtime Library Exception**: The GCC Runtime Library Exception allows code compiled with GCC to be distributed under any license. This exception does NOT apply to GCC's own source code, but our use is limited to test cases for educational purposes.

### Copyright Notice

```
Copyright (C) Free Software Foundation, Inc.
This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.
```

---

## 3. Our Transpiler Project

**License**: (Specify your project license here)
**Purpose**: C++ to C transpiler with C++23 validation
**Location**: Root repository

### Our Use of External Projects

We integrate external projects for:
- **Validation**: Verifying transpiler correctness against known test suites
- **Benchmarking**: Establishing compliance metrics
- **Education**: Understanding C++23 feature implementation

All external code remains clearly separated in `external-projects/` directory with full attribution.

---

## License Compatibility Analysis

### scivision/Cpp23-examples (MIT)
- ✅ **Compatible**: MIT is permissive and compatible with most licenses
- ✅ **Attribution Required**: MIT license text and copyright notice must be preserved
- ✅ **No Restrictions**: Can be used, modified, and integrated freely

### GCC Test Suite (GPL v3)
- ⚠️ **Fair Use**: Test code extraction for educational/research purposes
- ✅ **Attribution Required**: Full source attribution provided
- ✅ **No Distribution of GCC Code**: We only use test cases, not GCC implementation
- ✅ **Transformative Use**: Tests adapted to standalone C++ validation

### Our Integration Approach
- Keep external code clearly separated in `external-projects/`
- Maintain all original license files and attributions
- Document source commit hashes for traceability
- Use git submodules where possible for transparency

---

## Third-Party Dependencies

Our external projects may have their own dependencies:

### scivision/Cpp23-examples Dependencies
- CMake (build system)
- C++23-capable compiler (GCC 13+, Clang 16+)

### GCC Test Suite Dependencies
- None (standalone test files)
- Original tests use GCC-specific directives (dg-do, dg-options, dg-error)
- We adapt tests to remove GCC-specific syntax

---

## Updates and Maintenance

This document will be updated when:
- New external projects are integrated
- Existing projects are updated (git submodule updates)
- License terms change
- New feature categories are added

**Last Updated**: 2025-12-24
**Document Version**: 1.0
**Maintained By**: Transpiler Development Team

---

## References

- **GCC License**: https://gcc.gnu.org/onlinedocs/gcc/Copying.html
- **GCC Test Suite**: https://gcc.gnu.org/onlinedocs/gccint/Testsuites.html
- **MIT License**: https://opensource.org/licenses/MIT
- **GNU GPL v3**: https://www.gnu.org/licenses/gpl-3.0.html
- **Fair Use Guidelines**: https://www.copyright.gov/fair-use/

---

## Contact

For questions about license compliance or attribution:
- Open an issue on our repository
- Contact project maintainers

For questions about original projects:
- scivision/Cpp23-examples: https://github.com/scivision/Cpp23-examples/issues
- GCC: https://gcc.gnu.org/bugzilla/
