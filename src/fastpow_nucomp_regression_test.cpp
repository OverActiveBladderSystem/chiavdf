#include "fastpow_nucomp_checks.hpp"

#include <gtest/gtest.h>

#include <string>

TEST(FastPowNucompRegression, OneBitWindowBoundaryAliasKnownProofAndThreads) {
    std::string error;
    EXPECT_TRUE(RunFastPowNucompChecks(error)) << error;
}
