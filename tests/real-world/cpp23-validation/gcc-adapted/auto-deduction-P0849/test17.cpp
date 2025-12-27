// Generated from GCC test suite - Phase 33.2 C++23 Validation
// Original: auto-fncast4.C
// Category: auto-deduction
// Test ID: 17
//
// This file was automatically adapted from the GCC test suite.
// GCC-specific directives have been removed and code wrapped in standalone C++ format.
// See external-projects/gcc-tests/ for original sources.

// PR c++/103049
// P0849R8 - auto(x)

class cmdline_parser
{
    public:
    cmdline_parser(char const*);

    auto add_option(char const*, char const*) & -> cmdline_parser &;
    auto add_option(char const*, char const*) && -> cmdline_parser &&;

    void parse(int, char**);
};

int main(int argc, char *argv[])
{
    auto cmdline = cmdline_parser("driver");

    cmdline.add_option("-h", "show help messages")
           .add_option("-v", "show version");

    auto internal = auto(cmdline).add_option("--logging-level", "set logging level to 1-3")
                                 .add_option("--dump-full", "do not minimize dump");
    internal.parse(argc, argv);
}
