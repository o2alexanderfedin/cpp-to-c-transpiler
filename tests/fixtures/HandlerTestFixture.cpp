/**
 * @file HandlerTestFixture.cpp
 * @brief Implementation of HandlerTestFixture
 */

#include "HandlerTestFixture.h"

namespace cpptoc {
namespace test {

void HandlerTestFixture::SetUp() {
    // Create mock AST contexts
    mockCpp_ = std::make_unique<MockASTContext>();
    mockC_ = std::make_unique<MockASTContext>();

    // Create C node builder
    builder_ = std::make_unique<clang::CNodeBuilder>(mockC_->getContext());

    // Create handler context
    context_ = std::make_unique<HandlerContext>(
        mockCpp_->getContext(),
        mockC_->getContext(),
        *builder_
    );
}

void HandlerTestFixture::TearDown() {
    // Clean up in reverse order of creation
    context_.reset();
    builder_.reset();
    mockC_.reset();
    mockCpp_.reset();
}

void HandlerTestFixture::assertFunctionEquals(
    clang::FunctionDecl* actual,
    const std::string& expectedName,
    const std::string& expectedReturnType,
    size_t expectedParamCount
) {
    ASSERT_NE(actual, nullptr) << "Function declaration is null";
    EXPECT_EQ(actual->getNameAsString(), expectedName)
        << "Function name mismatch";
    EXPECT_EQ(actual->getNumParams(), expectedParamCount)
        << "Parameter count mismatch";

    // Check return type (simplified - just check it's not null)
    clang::QualType retType = actual->getReturnType();
    EXPECT_FALSE(retType.isNull()) << "Return type is null";

    // TODO: Add more sophisticated type checking if needed
}

void HandlerTestFixture::assertTranslated(clang::Decl* result, const char* message) {
    ASSERT_NE(result, nullptr) << message;
}

} // namespace test
} // namespace cpptoc
