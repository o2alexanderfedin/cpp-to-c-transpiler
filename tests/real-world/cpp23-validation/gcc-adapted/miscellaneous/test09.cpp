// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: Winvalid-utf8-6.C
// Category: miscellaneous
// Test ID: 09
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

int main()
{
  // P2295R6 - Support for UTF-8 as a portable source file encoding
// This test intentionally contains various byte sequences which are not valid UTF-8
char32_t a = U'';
char32_t b = U'¿';
char32_t c = U'À';
char32_t d = U'Á';
char32_t e = U'õ';
char32_t f = U'ÿ';
char32_t g = U'Â';
char32_t h = U'à';
char32_t i = U'à¿';
char32_t j = U'à';
char32_t k = U'à¿';
char32_t l = U'ì';
char32_t m = U'í ';
char32_t n = U'ð';
char32_t o = U'ð¿¿';
char32_t p = U'ô';
char32_t q = U'ý¿¿¿¿¿';
auto A = U"Âß¿à í¿îðô¿¿";
auto B = U"";
auto C = U"¿";
auto D = U"À";
auto E = U"Á";
auto F = U"õ";
auto G = U"ÿ";
auto H = U"Â";
auto I = U"à";
auto J = U"à¿";
auto K = U"à";
auto L = U"à¿";
auto M = U"ì";
auto N = U"í ";
auto O = U"ð";
auto P = U"ð¿¿";
auto Q = U"ô";
auto R = U"ý¿¿¿¿¿";
auto A1 = UR"(Âß¿à í¿îðô¿¿)";
auto B1 = UR"()";
auto C1 = UR"(¿)";
auto D1 = UR"(À)";
auto E1 = UR"(Á)";
auto F1 = UR"(õ)";
auto G1 = UR"(ÿ)";
auto H1 = UR"(Â)";
auto I1 = UR"(à)";
auto J1 = UR"(à¿)";
auto K1 = UR"(à)";
auto L1 = UR"(à¿)";
auto M1 = UR"(ì)";
auto N1 = UR"(í )";
auto O1 = UR"(ð)";
auto P1 = UR"(ð¿¿)";
auto Q1 = UR"(ô)";
auto R1 = UR"(ý¿¿¿¿¿)";
auto A2 = u8"Âß¿à í¿îðô¿¿";
auto B2 = u8"";
auto C2 = u8"¿";
auto D2 = u8"À";
auto E2 = u8"Á";
auto F2 = u8"õ";
auto G2 = u8"ÿ";
auto H2 = u8"Â";
auto I2 = u8"à";
auto J2 = u8"à¿";
auto K2 = u8"à";
auto L2 = u8"à¿";
auto M2 = u8"ì";
auto N2 = u8"í ";
auto O2 = u8"ð";
auto P2 = u8"ð¿¿";
auto Q2 = u8"ô";
auto R2 = u8"ý¿¿¿¿¿";
  return 0;
}
