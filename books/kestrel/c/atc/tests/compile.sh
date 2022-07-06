#!/usr/bin/env bash

################################################################################

# C Library
#
# Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Alessandro Coglio (coglio@kestrel.edu)

################################################################################

# This file compiles all the C files generated by ATC
# and all the handwritten test harness ATC files.

# This file assumes that GCC is in the path,
# as should be gnerally the case for macOS and Linux.

################################################################################

# stop on error:
set -e

# generate binaries
# (the -Wno-implicit-function-declaration option serves to prevent
# GCC on macOS from complaining about the generated functions
# called by the handwritten code without the former being declared;
# the proper way to handle this is by extending ATC to generate .h files
# and to include those in the handwritten files,
# but for now we simply suppress the error;
# GCC on Linux does not need this option, but it works fine with it):
gcc -Wno-implicit-function-declaration -o arrays arrays.c arrays-test.c
gcc -Wno-implicit-function-declaration -o assign assign.c assign-test.c
gcc -Wno-implicit-function-declaration -o calls calls.c calls-test.c
gcc -Wno-implicit-function-declaration -o checksum checksum.c checksum-test.c
gcc -Wno-implicit-function-declaration -o conditionals conditionals.c conditionals-test.c
gcc -Wno-implicit-function-declaration -o constants constants.c constants-test.c
gcc -Wno-implicit-function-declaration -o conversions conversions.c conversions-test.c
gcc -Wno-implicit-function-declaration -o int int.c int-test.c
gcc -Wno-implicit-function-declaration -o locvars locvars.c locvars-test.c
gcc -Wno-implicit-function-declaration -o loops loops.c loops-test.c
gcc -Wno-implicit-function-declaration -o mbt mbt.c mbt-test.c
gcc -Wno-implicit-function-declaration -o nonstrict nonstrict.c nonstrict-test.c
gcc -Wno-implicit-function-declaration -o not not.c not-test.c
gcc -Wno-implicit-function-declaration -o operators operators.c operators-test.c
gcc -Wno-implicit-function-declaration -o ops-diff-types ops-diff-types.c ops-diff-types-test.c
gcc -Wno-implicit-function-declaration -o structs structs.c structs-test.c
